/*
 * Copyright (c) 2004-2007 Sergey Lyubka <valenok@gmail.com>
 * All rights reserved
 *
 * "THE BEER-WARE LICENSE" (Revision 42):
 * Sergey Lyubka wrote this file.  As long as you retain this notice you
 * can do whatever you want with this stuff. If we meet some day, and you think
 * this stuff is worth it, you can buy me a beer in return.
 *
 * $Id$
 */

#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>
#include <setjmp.h>
#include <stddef.h>
#include <errno.h>

#define	MAX_SOURCE_SIZE		32768	/* Maximum source file size	*/
#define	CHUNK_SIZE		64	/* Runtime stack growing size	*/
#define	ERR_STR_SIZE		256	/* Error buffer size		*/
#define	HASH_SIZE		13	/* Hash object hash table size	*/
#define	PCODE_MAGIC		"ABC1"	/* Compiled p-code signature	*/
#define	MAX_EXPR_TOKS		512	/* Maximum tokens in expression	*/

#define	ARRAY_SIZE(array)	((int) (sizeof(array) / sizeof(array[0])))

struct q;
struct obj;

/*
 * Circular doubly-linked list macros: http://silversoft.net/~devnull/llist.h
 */
struct llhead {
	struct llhead	*next;
	struct llhead	*prev;
};

#define	LL_INIT(N)	((N)->next = (N)->prev = (N))
#define LL_HEAD(H)	struct llhead H = {&H, &H}
#define	LL_NULL		{NULL, NULL}
#define LL_ENTRY(P,T,N) ((T *)((char *)(P) - offsetof(T, N)))

#define	LL_ADD(H, N)							\
	do {								\
		((H)->next)->prev = (N);				\
		(N)->next = ((H)->next);				\
		(N)->prev = (H);					\
		(H)->next = (N);					\
	} while (0)

#define	LL_TAIL(H, N)							\
	do {								\
		((H)->prev)->next = (N);				\
		(N)->prev = ((H)->prev);				\
		(N)->next = (H);					\
		(H)->prev = (N);					\
	} while (0)

#define	LL_DEL(N)							\
	do {								\
		((N)->next)->prev = ((N)->prev);			\
		((N)->prev)->next = ((N)->next);			\
		LL_INIT(N);						\
	} while (0)

#define	LL_EMPTY(N)	((N)->next == (N))

#define	LL_FOREACH(H,N)	for (N = (H)->next; N != (H); N = (N)->next)

#define LL_FOREACH_SAFE(H,N,T)						\
	for (N = (H)->next, T = (N)->next; N != (H);			\
			N = (T), T = (N)->next)

struct hash {
	struct obj	*parent;	/* Parent object		*/
	struct llhead	glob_list;	/* For all entries in the hash	*/
	struct llhead	tab[HASH_SIZE];	/* Hash table itself		*/
};

/*
 * Typedefs to abstract environment-specific types
 */
typedef void	(*q_op_handler_t)(struct q *);
typedef double	numeric_t;		/* Type for numeric values	*/
typedef size_t	str_size_t;		/* For string lengths		*/
typedef int	code_ofs_t;		/* For relative JUMP operands	*/

/*
 * Strings are arbitrary chunks of uninterpreted binary data.
 * Represented by a pointer to data and data length in bytes.
 */
struct vec {
	int		len;		/* Length of binary data	*/
	char		*ptr;		/* Pointer to binary data	*/
};

/*
 * Value of any supported type
 */
union val {
	struct vec	str;		/* String value			*/
	q_op_handler_t	cfunc;		/* Function implemented in C	*/
	struct hash	*hash;		/* Hash value			*/
	numeric_t	num;		/* Numeric value		*/
	code_ofs_t	ofs;		/* Jump offset value		*/
};

/*
 * Object. This is a type marker and associated value.
 */
struct obj {
	unsigned char	type;		/* TYPE_XXX, see below		*/
	union val	val;		/* Value holder			*/
};

/*
 * Hash entry
 */
struct he {
	struct llhead	link;		/* Hash cell linkage		*/
	struct obj	key;		/* Entry' key			*/
	struct obj	val;		/* Entry's value		*/
};

/*
 * Q context
 */
struct q {
	struct llhead	link;		/* Linkage			*/
	char		*name;		/* Module name			*/
	char		*code;		/* Code				*/
	struct obj	*stack;		/* Stack			*/
	int		sc;		/* Stack counter		*/
	int		fc;		/* Call frame pointer		*/
	int		cc;		/* Code counter			*/
	int		cs;		/* Code size			*/
	int		ss;		/* Stack size			*/
	jmp_buf		jmpbuf;		/* Exception environ		*/
	char		*err_str;	/* Error message placeholder	*/
};

/*
 * This is a parse token and syntax tree node at the same time
 */
struct node {
	struct llhead	link;		/* Linkage in expression	*/
	struct vec	vec;		/* Points to the source code	*/
	int		tok;		/* Token's value		*/
	int		line_no;	/* Line number in the source	*/
	struct node	*left;
	struct node	*right;
	struct node	*parent;
};

/*
 * Types and their names
 */
enum {TYPE_NIL, TYPE_NUM, TYPE_STR, TYPE_HASH, TYPE_FUNC, TYPE_CFUNC};
static const char *types[] = {"nil", "num", "str", "hash", "func", "c-func"};

/*
 * Opcodes and their names. Names are prepended by a letter that specifies
 * opcode parameters (used by disassembly function)
 */
enum {
	OP_END, OP_CALL, OP_RETURN, OP_SET, OP_GET, OP_PUSH, OP_MATH,
	OP_POP, OP_JUMP, OP_DUP, OP_PUSHNS, OP_NEWMAP, NUM_INSTTRUCTIONS
};

static const char *opcodes[] = {
	"xEND", "xCALL", "xRETURN", "xSET", "xGET", "tPUSH", "aMATH",
	"xPOP", "xJUMP", "nDUP", "xPUSHNS", "xNEWMAP"
};

static const char *serr = "syntax error";
static const char *rerr = "runtime error";

/*
 * Tokens. XXX Make sure that long token values do not clash with one char.
 * We start numbering long tokens from 'a', which gives us at least
 * 26 English letters; there are no letters in one char tokens.
 */
static const char *one_char_tokens = "=[](){}+-*/^,;.\"";

enum {
	TOK_IDENT = 'a', TOK_NUM, TOK_STR, TOK_FUNC, TOK_IF, TOK_ELSE,
	TOK_ADDE, TOK_SUBE, TOK_MULE, TOK_DIVE, TOK_NIL, TOK_NOT,
	TOK_AND, TOK_OR,
	/* XXX up to this point, must be parallel to long_tokens[] */
	TOK_END
};

static const char *long_tokens[] = {
	"%v", "%d", "%s", "function", "if", "else", "+=", "-=", "*=", "/=",
	"nil", "not", "and", "or", NULL
};

static LL_HEAD(loaded_modules);

static void die(struct q *q, const char *fmt, ...)
{
	va_list	ap;

	va_start(ap, fmt);
	(void) vsnprintf(q->err_str, ERR_STR_SIZE, fmt, ap);
	va_end(ap);

	longjmp(q->jmpbuf, 1);
}

static void expand_code(struct q *q, int len)
{
	q->cs += len;
	q->code = realloc(q->code, q->cs);
	if (q->code == NULL)
		die(q, "%s: cannot grow code to %u bytes", serr, q->cs);
}

static void emit(struct q *q, const void *mem, int len)
{
	if (q->code == NULL || q->cc + len >= q->cs)
		expand_code(q, CHUNK_SIZE);

	(void) memcpy(q->code + q->cc, mem, len);
	q->cc += len;
}

static void emit_byte(struct q *q, unsigned char value)
{
	emit(q, &value, sizeof(value));
}

static void emit_num(struct q *q, numeric_t val)
{
	emit_byte(q, OP_PUSH);
	emit_byte(q, TYPE_NUM);
	emit(q, &val, sizeof(val));
}

static const int hex_tab[] = {
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, -1, -1, -1, -1, -1, -1,
	-1, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
	-1, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1
};

static int hex_ascii_to_int(struct q *q, unsigned char ch, int line_no)
{
	if (ch >= ARRAY_SIZE(hex_tab) || hex_tab[ch] == -1)
		die(q, "%s: line %d: badly encoded string", serr, line_no);
	return (hex_tab[ch]);
}

static void emit_string_constant(struct q *q, const struct node *node)
{
	char			*dst, *src;
	str_size_t		n = 0;

	/* XXX Must go first, cause expand_code may change q->code pointer */
	if (q->code + q->cc + 2 + sizeof(n) + node->vec.len > q->code + q->cs)
		expand_code(q, node->vec.len + 2 + sizeof(n) + 1);

	dst = q->code + q->cc + 2 + sizeof(n);
	src = node->vec.ptr + 1;

	assert(node->vec.ptr[0] == '"');
       	assert(node->vec.ptr[node->vec.len - 1] == '"');
	assert(dst + node->vec.len < q->code + q->cs);

	for (; src < node->vec.ptr + node->vec.len - 1; src++, n++)
		if (*src == '%') {
			dst[n] = hex_ascii_to_int(q,src[1],node->line_no) << 4;
			dst[n] |= hex_ascii_to_int(q, src[2], node->line_no);
			src += 2;
		} else {
			dst[n] = *src;
		}

	emit_byte(q, OP_PUSH);
	emit_byte(q, TYPE_STR);
	emit(q, &n, sizeof(n));
	q->cc += n;
}

/*
 * Operator attributes table. Operator's token is an index in this table.
 * The value stored is an integer, where:
 *  o least significant byte is operator's priority
 *  o next byte is a number of operands
 *  o next byte is a flag, whether operator is right-to-left, like '='
 */
static int op_tab[256];

static int set_op_attributes(int priority, int num_args, int is_right_to_left)
{
	return (priority | (num_args << 8) | (is_right_to_left << 16));
}

static void init_op_tab(void)
{
	op_tab['.'] = op_tab['('] = set_op_attributes(100, 2, 0);
	op_tab['['] = set_op_attributes(100, 1, 1);
	op_tab['*'] = op_tab['/'] = op_tab['%'] = set_op_attributes(80, 2, 0);
	op_tab['+'] = op_tab['-'] = set_op_attributes(60, 2, 0);
	op_tab['='] = op_tab[TOK_ADDE] = op_tab[TOK_SUBE] =
	    op_tab[TOK_MULE] = op_tab[TOK_DIVE] = set_op_attributes(20, 2, 1);
	op_tab[','] = set_op_attributes(10, 2, 0);
}

/*
 * Shortcut functions to access operator attributes
 */
static int prio(int tok)	{ return (op_tab[tok] & 0xff);		}
static int nargs(int tok)	{ return ((op_tab[tok] >> 8) & 0xff);	}
static int is_rtl(int tok)	{ return ((op_tab[tok] >> 16) & 0xff);	}
static int is_op(int tok)	{ return (op_tab[tok]);			}

static int calc_number_of_params(const struct node *node, int n)
{
	if (node->left)
		n += calc_number_of_params(node->left, 0);
	if (node->right)
		n += calc_number_of_params(node->right, 0);
	if (node->tok == ',')
		n++;

	return (n);
}

static int is_lvalue(const struct node *node)
{
	return (node->parent != NULL && node->parent->tok == '=' &&
	    node->parent->left == node);
}

static int is_leftmost(const struct node *node)
{
	if (node->parent != NULL && node->parent->left == node &&
	    node->parent->tok == '=') {
		return (1);
	} else if (node->parent != NULL && node->parent->left == node &&
	    node->parent->tok == '.') {
		return (is_leftmost(node->parent));
	} else {
		return (0);
	}
}

static void emit_ident(struct q *q, const struct node *node)
{
	emit_byte(q, OP_PUSH);
	emit_byte(q, TYPE_STR);
	emit(q, &node->vec.len, sizeof(node->vec.len));
	emit(q, node->vec.ptr, node->vec.len);
}
			

static void emit_expr(struct q *, const struct node *);

static void emit_hash_definition(struct q *q, const struct node *node, int idx)
{
	if (node == NULL) {
		die(q, "%s: line %d: bad hash def", serr, node->line_no);
	} else if (node->tok == ',') {
		emit_hash_definition(q, node->left, idx);
		emit_byte(q, OP_POP);
		emit_hash_definition(q, node->right, idx + 1);
	} else if (node->tok == '=') {
		if (node->left->tok == TOK_IDENT) {
			emit_expr(q, node->right);
			emit_byte(q, OP_DUP);
			emit_byte(q, 1);
			emit_ident(q, node->left);
			emit_byte(q, OP_SET);
		} else {
			die(q, "%s: line %d: bad hash def", serr,node->line_no);
		}
	} else {
		/* Key is the index of the entry in the definition */
		emit_expr(q, node);
		emit_byte(q, OP_DUP);
		emit_byte(q, 1);
		emit_num(q, idx);
		emit_byte(q, OP_SET);
	}
}

static int emit_params(struct q *q, const struct node *node, int n)
{
	if (node->tok == TOK_NIL) {
		/* Do nothing - no parameters passed to function */
	} else if (node->tok == ',') {
		n = emit_params(q, node->left, n);
		n = emit_params(q, node->right, n);
	} else {
		emit_expr(q, node);
		n++;
	}

	return (n);
}

static void emit_function_call(struct q *q, const struct node *node)
{
	int	num_params;

	num_params = emit_params(q, node->right, 0);
	emit_num(q, num_params);
	emit_expr(q, node->left);
	emit_byte(q, OP_CALL);
}

static void emit_expr(struct q *q, const struct node *node)
{
	switch (node->tok) {

	case '.':
		if (node->left->tok == TOK_IDENT)
			emit_byte(q, OP_PUSHNS);
		emit_expr(q, node->left);
		emit_expr(q, node->right);
		emit_byte(q, OP_GET);
		break;

	case '%':
	case '*':
	case '/':
	case '+':
	case '-':
		emit_expr(q, node->left);
		emit_expr(q, node->right);
		emit_byte(q, OP_MATH);
		emit_byte(q, node->tok);
		break;

	case '=':
		emit_expr(q, node->right);
		emit_expr(q, node->left);
		if (node->left->tok != TOK_IDENT &&
		    node->left->tok != '.' && node->left->tok != '=')
			die(q, "%s: %d: %s", serr,
			    node->line_no, "invalid assignment");
		emit_byte(q, OP_SET);
		break;

	case ',':
		emit_expr(q, node->left);
		emit_expr(q, node->right);
		die(q, "%s: %d: %s", serr, node->line_no, "use ';', not ','");
		break;

	case '(':
		emit_function_call(q, node);
		break;

	case TOK_NIL:
		emit_byte(q, OP_PUSH);
		emit_byte(q, TYPE_NIL);
		break;

	case TOK_IDENT:
		/*
		 * Identifier could be either rvalue or lvalue:
		 * "foo.bar = baz = x.y;"
		 * Lvalues: bar, baz
		 * Rvalues: foo, x, y
		 * Lvalue is a key, for namespace insert.
		 * Rvalue is always a key for namespace lookup.
		 */
		if (node->parent == NULL || node->parent->tok != '.')
			emit_byte(q, OP_PUSHNS);
		emit_ident(q, node);
		if (!is_lvalue(node) && !(node->parent != NULL &&
		    node->parent->tok == '.' && is_lvalue(node->parent)))
			emit_byte(q, OP_GET);
		break;

	case TOK_STR:
		emit_string_constant(q, node);
		break;

	case TOK_NUM:
		emit_num(q, strtod(node->vec.ptr, NULL));
		break;

	case '[':
		emit_byte(q, OP_NEWMAP);
		assert(node->right != NULL);
		if (node->right->tok != TOK_NIL) {
			emit_hash_definition(q, node->right, 0);
			emit_byte(q, OP_POP);
		}
		break;

	default:
		die(q, "%s: %d: %s [%d]", serr, node->line_no,
		    "internal parser error", node->tok);
		break;
	}
}

static int cmp_vec(const struct vec *a, const struct vec *b)
{
	int	rc;

	if (a->len < b->len)
		return (-cmp_vec(b, a));

	rc = memcmp(a->ptr, b->ptr, b->len);
	if (rc == 0)
		rc = a->len - b->len;

	return (rc);
}

static int cmp(const struct obj *a, const struct obj *b)
{
	int	res = 0;

	assert(a->type == b->type);

	switch (a->type) {
	case TYPE_NIL:
		break;
	case TYPE_NUM:
		res = a->val.num - b->val.num;
		break;
	case TYPE_STR:
		res = cmp_vec(&a->val.str, &b->val.str);
		break;
	case TYPE_CFUNC:
		break;
	case TYPE_FUNC:
		res = a->val.cfunc == b->val.cfunc ? 0 : 1;
		break;
	case TYPE_HASH:
		res = a->val.hash == b->val.hash ? 0 : 1;
		break;
	default:
		abort();
		break;
	}

	return (res);
}

static unsigned long hash_str(unsigned long hash, const struct vec *vec)
{
	int	i;

	for (i = 0; i < vec->len; i++)
		hash = (hash << 5) - hash + vec->ptr[i];

	return (hash);
}

static unsigned long calc_hash(const struct obj *obj)
{
	unsigned long	hash = obj->type;

	switch (obj->type) {
	case TYPE_NIL:
		break;
	case TYPE_NUM:
		hash += (unsigned long) obj->val.num;
		break;
	case TYPE_STR:
		hash = hash_str(hash, &obj->val.str);
		break;
	case TYPE_CFUNC:
		hash += (unsigned long) obj->val.ofs;
		break;
	case TYPE_FUNC:
		hash += (unsigned long) obj->val.cfunc;
		break;
	case TYPE_HASH:
		break;
	default:
		abort();
		break;
	}

	return (hash);
}

static struct he *lookup(struct obj *obj, struct obj *key, size_t *pcell)
{
	struct llhead	*lp, *head;
	struct hash	*hash;
	struct he	*he;
	size_t		cell;

	assert(obj->type == TYPE_HASH);
	hash = obj->val.hash;

	cell = calc_hash(key) % ARRAY_SIZE(hash->tab);
	head = hash->tab + cell;

	if (pcell != NULL)
		*pcell = cell;

	LL_FOREACH(head, lp) {
		he = LL_ENTRY(lp, struct he, link);
		if (he->key.type == key->type && cmp(&he->key, key) == 0)
			return(he);
	}

	return (NULL);
}

static struct obj *lookup_ins(struct obj *obj, struct obj *key, struct obj *val)
{
	struct he	*he;
	struct hash	*hash;
	size_t		cell;

	hash = obj->val.hash;

	if ((he = lookup(obj, key, &cell)) == NULL) {
		he = calloc(1, sizeof(*he));
		he->key = *key;
		if (val != NULL)
			he->val = *val;
		LL_TAIL(hash->tab + cell, &he->link);
	}

	return (&he->val);
}

static struct obj *lookup_rec(struct q *q, struct obj *obj, struct obj *key)
{
	struct he	*he;

	while (obj != NULL) {
		if (obj->type != TYPE_HASH)
			die(q, "%s: %d: attempt to get an attribute from the"
			    " <%s> object", rerr, q->cc, types[obj->type]);
		else if ((he = lookup(obj, key, NULL)) != NULL)
			return (&he->val);

		/* This lookup is recursive. Switch to the parent object */
		obj = obj->val.hash->parent;
	}

	return (NULL);
}

static struct obj *pop(struct q *q)
{
	if (--q->sc < 0)
		die(q, "%s: %d: %s", rerr, q->cc, "stack underflow");
	return (q->stack + q->sc);
}

static struct obj *push(struct q *q)
{
	if (q->stack == NULL || q->sc >= (int) q->ss) {
		q->ss += CHUNK_SIZE;
		q->stack = realloc(q->stack, q->ss * sizeof(q->stack[0]));
	}

	if (q->stack == NULL)
		die(q, "%s: %d: %s %u", rerr, q->cc,
		    "cannot grow stack to %u", q->ss);

	return (q->stack + q->sc++);
}


static void init_hash_obj(struct obj *obj, struct obj *parent)
{
	struct hash	*hash;
	size_t		i;

	obj->type	= TYPE_HASH;
	obj->val.hash	= hash = malloc(sizeof(*obj->val.hash));
	hash->parent	= parent;

	LL_INIT(&hash->glob_list);
	for (i = 0; i < ARRAY_SIZE(hash->tab); i++)
		LL_INIT(hash->tab + i);
}

/*
 * Get integer value from stack, at relative offset stack_ofs
 */
static int gsi(struct q *q, int stack_ofs)
{
	const struct obj	*obj = q->stack + q->sc - 1 - stack_ofs;

	if (obj < q->stack)
		die(q, "%s: %d: stack underflow", rerr, q->cc);
	else if (obj->type != TYPE_NUM)
		die(q, "%s: %d: expected number on stack", rerr, q->cc);

	return ((int) obj->val.num);
}

static void execute(struct q *q)
{
	const char	*c = q->code + q->cc;
	struct obj	*obj, *val, *key, *a, *b;

	while (*c != OP_END) {

		q->cc = c - q->code;
		if (q->cc >= (int) q->cs)
			die(q, "%s", "corrupt code");
#if 0
		printf("%d: sc %d (%s)\n",
		    q->cc, q->sc, types[q->stack[q->sc - 1].type]);
#endif

		switch (*c++) {

		case OP_CALL: /* ( -- ret_addr old_fc new_namespace) */
			obj = pop(q);
			if (obj->type == TYPE_CFUNC) {
				obj->val.cfunc(q);
				q->sc -= obj[-1].val.num + 1;
			} else if (obj->type == TYPE_FUNC) {
				/* TODO - implement native functions */
			} else {
				die(q, "%s: %d: attempt to call <%s> object",
				    rerr, q->cc, types[obj->type]);
			}
			break;

		case OP_RETURN:
			break;

		case OP_SET:	/* (val obj key -- val) */
			key = pop(q);
			obj = pop(q);
			val = pop(q);
			if (obj->type != TYPE_HASH)
				die(q, "%s: %d: attemt to set "
				    "an attribute to <%s> object",
				    rerr, q->cc, types[obj->type]);
			(void) lookup_ins(obj, key, val);
			q->sc++;
			break;

		case OP_GET:	/* (obj key -- val) */
			key = pop(q);
			obj = pop(q);
			if ((val = lookup_rec(q, obj, key)) != NULL)
				*obj = *val;
			else
				obj->type = TYPE_NIL;
			q->sc++;
			break;

		case OP_PUSH:	/* ( -- val) */
			obj = push(q);
			obj->type = *c++;

			switch (obj->type) {
			case TYPE_NUM:
				obj->val.num = * (numeric_t *) c;
				c += sizeof(numeric_t);
				break;
			case TYPE_STR:
				obj->val.str.len = * (str_size_t *) c;
				c += sizeof(str_size_t);
				obj->val.str.ptr = (char *) c;
				c += obj->val.str.len;
				break;
			case TYPE_HASH:
				init_hash_obj(obj, NULL);
				break;
			case TYPE_NIL:
				break;
			default:
				die(q, "%s: %d: %s", rerr, q->cc,
				    "attempt to PUSH an unknown shit");
				abort();
			break;
			}
			break;

		case OP_MATH:	/* (val1 val2 -- result) */
			b = pop(q);
			a = pop(q);

			if (a->type != TYPE_NUM || b->type != TYPE_NUM)
				die(q, "%s: %d: <%s> found, <num> expected",
				    rerr, q->cc, types[a->type]);

			switch (*c++) {
			case '+': a->val.num += b->val.num; break;
			case '-': a->val.num -= b->val.num; break;
			case '*': a->val.num *= b->val.num; break;
			case '/':
				if (b->val.num == 0)
					die(q, "%s: %d: %s",
					    rerr, q->cc, "division by zero");
				a->val.num /= b->val.num;
				break;
			default:
				die(q, "%s: %d: unexpected arith operator: %u",
				    rerr, q->cc, c[-1]);
				break;
			}
			q->sc++;
			break;

		case OP_POP:	/* (obj --) */
			(void) pop(q);
			break;

		case OP_DUP:	/* (-- obj) */
			if (q->sc <= *c)
				die(q, "%s: stack underflow", rerr);
			obj = q->stack + q->sc - 1 - *c++;
			val = push(q);
			*val = *obj;
			break;

		case OP_JUMP:	/* (--) */
			break;

		case OP_PUSHNS:
			obj = push(q);
			obj->type = TYPE_HASH;
			obj->val.hash = q->stack[q->fc].val.hash;
			break;

		case OP_NEWMAP:	/* (-- hash_obj) */
			obj = push(q);
			init_hash_obj(obj, &q->stack[q->fc]);
			break;

		default:
			die(q, "%s: %d: %s", rerr, q->cc, "corrupter code");
			break;
		}
	}
}

static void disasm(struct q *q)
{
	const char	*name, *c;
	int		len;

	for (c = q->code; *c != OP_END; c++) {

		assert(NUM_INSTTRUCTIONS == ARRAY_SIZE(opcodes));
		assert(*c < NUM_INSTTRUCTIONS);

		name = opcodes[(int) *c];
		printf("%-4d %s", c - q->code, name + 1);

		if (name[0] == 'a') {
			printf(" %c", *++c);
		} else if (name[0] == 'n') {
			printf(" %d", *++c);
		} else if (name[0] == 't') {
			printf(" <%s> ", types[(int) *++c]);
			switch (*c) {
			case TYPE_NIL:
				break;
			case TYPE_NUM:
				printf("%.2f", (double) *(numeric_t *)(c + 1));
				c += sizeof(numeric_t);
				break;
			case TYPE_STR:
				len = * (str_size_t *) (c + 1);
				c += sizeof(str_size_t);
				printf("\"%.*s\"", (int) len, c + 1);
				c += len;
				break;
			default:
				break;
			}
		}

		(void) putchar('\n');
	}
}

static void print_obj(const struct obj *obj)
{
	switch (obj->type) {
	case TYPE_STR:
		printf("%.*s", (int) obj->val.str.len, obj->val.str.ptr);
		break;
	case TYPE_NUM:
		printf("%.2f", (double) obj->val.num);
		break;
	default:
		printf("<%s>", types[obj->type]);
		break;
	}
}

static void print(struct q *q)
{
	int		i, param_count = gsi(q, 0);
	struct obj	*obj = q->stack + q->sc - param_count - 1;

	for (i = 0; i < param_count; i++, obj++)
		print_obj(obj);
}

static void q_free(struct q *q)
{
	if (q != NULL) {
		if (q->code != NULL)
			free(q->code);
		if (q->stack != NULL)
			free(q->stack);
		if (q->name != NULL)
			free(q->name);
		free(q);
	}
}

static struct obj *setattr(struct obj *obj, const char *name, struct obj *attr)
{
	struct obj	key;

	key.type	= TYPE_STR;
	key.val.str.ptr	= (char *) name;
	key.val.str.len	= strlen(name);

	return (lookup_ins(obj, &key, attr));
}

static void import_builtin_objects(struct q *q)
{
	struct obj	obj, *namespace = q->stack;

	obj.type = TYPE_CFUNC;
	obj.val.cfunc = &print;
	setattr(namespace, "print", &obj);
	obj.val.cfunc = &disasm;
	setattr(namespace, "disasm", &obj);
}

static void q_save(const char *path, const struct q *q, char *err_str)
{
	FILE	*fp;

	if ((fp = fopen(path, "w+")) == NULL) {
		(void) snprintf(err_str, ERR_STR_SIZE,
		    "fopen(%s): %s", path, strerror(errno));
	} else {
		(void) fwrite(PCODE_MAGIC, 1, sizeof(PCODE_MAGIC) - 1, fp);
		(void) fwrite(q->code, 1, q->cs, fp);
		(void) fclose(fp);
	}
}

static int match_long_token(const char *str, const char *in)
{
	int	len = 0;
	char	*end;

	if (str[0] == '%' && str[1] == 'v') {
		if (*in == '_' || isalpha(* (unsigned char *) in))
			while (in[len] == '_' ||
			    isalnum(((unsigned char *)in)[len]))
				len++;
	} else if (str[0] == '%' && str[1] == 'd') {
		(void) strtod(in, &end);
		len = end - in;
	} else if (str[0] == '%' && str[1] == 's') {
		if (*in == '"' && (end = strchr(in + 1, '"')) != NULL)
			len = end - in + 1;
	} else if (strncmp(in, str, strlen(str)) == 0) {
		len = strlen(str);
	}

	return (len);
}

/* 
 * Parse the file, calling user function for every token.
 * Return total number of tokens, including last TOK_END.
 */
static int tokenize(const char *buf, struct node *nodes)
{
	struct node	*node;
	const char	*cp;
	int		i, line_no = 1, num_nodes = 0;

	do {
		/* Skip whitespaces and comments, counting line numbers */
again:		for (; isspace(*(unsigned char *) buf); buf++)
			if (*buf == '\n')
				line_no++;
		if (*buf == '#')
			for (buf++; *buf != '\0'; buf++)
				if (*buf == '\n')
					goto again;

		/* Initialize node */
		node		= nodes + num_nodes++;
		(void) memset(node, 0, sizeof(struct node));
		node->vec.ptr	= (char *) buf;
		node->line_no	= line_no;
		node->tok	= TOK_END;

		/* Try to match one of the long tokens */
		for (i = 0; long_tokens[i] != NULL; i++)
			if ((node->vec.len =
			    match_long_token(long_tokens[i], buf)) > 0) {
				node->tok = TOK_IDENT + i;
				break;
			}

		/* Try to match one character token */
		if (node->vec.len == 0 && *buf != '\0' &&
		    ((cp = strchr(one_char_tokens, *buf))) != NULL) {
			node->tok = *cp;
			node->vec.len = 1;
		}

		buf += node->vec.len;
#if 0
		printf("tok %d: [%.*s]\n",
		    node->tok, node->vec.len, node->vec.ptr);
#endif
	} while (node->tok != TOK_END);

	return (num_nodes);
}

static void bubble_sort_ops_by_priority(struct node **ops, int num_ops)
{
	struct node	*tmp;
	int		i, swapped;

	/*
	 * All left-to-right nodes must be sorted by priority. Sorting is
	 * stable, i.e. the order is not broken for the nodes of equal
	 * priority. We *DO* break the order for the right-to-left nodes,
	 * though. So same-prio RTL nodes are reversed.
	 */
	do {
		swapped = 0;
		for (i = 0; i < num_ops - 1; i ++)
			if ((is_rtl(ops[i]->tok) && is_rtl(ops[i + 1]->tok) &&
			    prio(ops[i]->tok) == prio(ops[i + 1]->tok) &&
			    ops[i] < ops[i + 1]) ||
			    (prio(ops[i]->tok)  < prio(ops[i + 1]->tok))) {
				tmp = ops[i];
				ops[i] = ops[i + 1];
				ops[i + 1] = tmp;
				swapped = 1;
			}
	} while (swapped == 1);
}

static void reduce(struct q *q, struct node *parent, int ano, struct llhead *h)
{
	int		take_from_left;
	struct llhead	*lp;
	struct node	*node;

	assert(is_op(parent->tok));

	/* Figure out which node to take - from the left or from the right */
	take_from_left = !ano ^ is_rtl(parent->tok);
	lp = take_from_left ? parent->link.prev : parent->link.next;
	node = LL_ENTRY(lp, struct node, link);

	/*
	 * Make sure the node pointer points to the real node. It may not
	 * point to the real node if parent is:
	 *  - first in the expression and is left-to-right
	 *  - last in the expression and is right-to-left
	 * In these (erroneous) cases, 'lp' points to the list head,
	 * not node's link.
	 */
	if (lp == h)
		die(q, "%s: line %d", serr, node->line_no);

	/*
	 * Delete operand from the expession list, and append it
	 * respectively to the left or right branch in the parent.
	 */
	LL_DEL(&node->link);
	if (take_from_left)
		parent->left = node;
	else
		parent->right = node;
	node->parent = parent;
}

static int qaz(const struct node *node, int num_nodes)
{
	int	prev_tok = node[-1].tok;

	return (num_nodes > 1 &&
	    (prev_tok == TOK_IDENT || prev_tok == ']' || prev_tok == ')'));
}

static int expr(struct q *q, struct node *tab, int endtok, struct node **root)
{
	static struct node	nil;
	struct node		*ops[MAX_EXPR_TOKS], *node, *tmp;
	struct llhead		head;
	int			i, j, num_toks, num_ops;

	nil.tok = TOK_NIL;
	LL_INIT(&head);
	num_toks = num_ops = 0;

	/*
	 * Scan the expression until end token reached. Link all tokens
	 * into one list. Insert operations into ops array. We'll use list
	 * and ops array to build the syntax tree for the expression.
	 */
	while (tab[num_toks].tok != endtok) {

		/* Link that node into expression's list */
		node = tab + num_toks++;
		LL_TAIL(&head, &node->link);

		if (node->tok == TOK_END) {
			die(q, "line %d: unexpected EOF", node->line_no);
		} else if (node->tok == '(' || node->tok == '[') {
			/* Disambiguate () and [] operators */
			if (node->tok == '(' && !qaz(node, num_toks))
				LL_DEL(&node->link);
			else if (node->tok == '[' && qaz(node, num_toks))
				node->tok = '.';
			num_toks += expr(q, node + 1,
			    node->tok == '(' ?  ')' : ']', &tmp);
			LL_TAIL(&head,	 &tmp->link);
		}

		if (is_op(node->tok))
			ops[num_ops++] = node;
	}

	/* Reduce token list into a syntax tree */
	bubble_sort_ops_by_priority(ops, num_ops);
	for (i = 0; i < num_ops; i++)
		for (j = 0; j < nargs(ops[i]->tok); j++)
			reduce(q, ops[i], j, &head);

	/* 
	 * Exactly one node must left linked next to the list head,
	 * and that one is the root of the tree. If num_nodes is 0, then
	 * the expression is empty. In this case NIL node is returned as root.
	 */
	if (head.next != head.prev)
		die(q, "%s: line %d: %s", serr, node->line_no, "bad expr");	
	*root = num_toks == 0 ? &nil : LL_ENTRY(head.next, struct node, link);

	return (num_toks + 1);	/* +1 is for the end-token */
}

static void q_exec_string(struct q *q, const char *buf)
{
	struct node	pool[MAX_SOURCE_SIZE], *root;
	int		idx = 0;

	/* Allocate an array of tokens on the stack, and tokenize the source */
	tokenize(buf, pool);

	/* Build syntax tree for each top-level statement */
	while (pool[idx].tok != TOK_END) {
		idx += expr(q, pool + idx, ';', &root);
		emit_expr(q, root);
		emit_byte(q, OP_POP);
	}

	/* Finish compilation */
	emit_byte(q, OP_END);
}

static void compile(struct q *q, const char *path)
{
	char		buf[MAX_SOURCE_SIZE];
	int		n = 0;
	FILE		*fp;

	/* Read whole source file in buffer */
	if ((fp = fopen(path, "r")) == NULL) {
		die(q, "fopen(%s): %s", path, strerror(errno));
	} else if ((n = fread(buf, 1, sizeof(buf), fp)) < 0) {
		die(q, "fread(%s): %s", path, strerror(errno));
	} else if (n == sizeof(buf)) {
		die(q, "%s: file is too large", path);
	}

	/* \0 terminate it the buffer, so tokenizer knows where to stop */
	buf[n] = '\0';
	(void) fclose(fp);

	q_exec_string(q, buf);

	/* Initialize namespace hash. */
	init_hash_obj(push(q), NULL);
	assert(q->sc == 1);
	import_builtin_objects(q);

	/* Point to the start of the code */
	disasm(q);
	q->cc = 0;
	execute(q);

	LL_ADD(&loaded_modules, &q->link);
}

static struct q *q_load(const char *path, char *err_str)
{
	struct llhead	*lp;
	struct q	*q;

	/* Maybe this module is already loaded? */
	LL_FOREACH(&loaded_modules, lp) {
		q = LL_ENTRY(lp, struct q, link);
		if (strcmp(q->name, path) == 0)
			return (q);	/* Yeah */
	}

	/* No, not loaded yet. Load it now. */
	if ((q = calloc(1, sizeof(*q))) == NULL) {
		(void) snprintf(err_str, ERR_STR_SIZE, "%s",
		    "cannot allocate memory for q");
	} else if (setjmp(q->jmpbuf) != 0) {
		q_free(q);
		q = NULL;
	} else {
		q->err_str = err_str;
		q->name = strdup(path);
		compile(q, path);
	}

	return (q);
}

static void usage(void)
{
	(void) fprintf(stderr, "usage: qq [-c <file>] file\n");
	exit(EXIT_FAILURE);
}

static const char *get_opt(int *pargc, char ***pargv)
{
	const char      *opt;

	if ((*pargv)[1][2] != '\0') {
		opt = &(*pargv)[1][2];
		(*pargc)--;
		(*pargv)++;
	} else {
		opt = (*pargv)[2];
		(*pargc) -= 2;
		(*pargv) += 2;
	}

	if (opt == NULL)
		usage();

	return (opt);
}

int main(int argc, char *argv[])
{
	char		err_str[ERR_STR_SIZE];
	const char	*pcode_file = NULL;
	struct q	*q;

	while (argc > 1 && argv[1][0] == '-' && argv[1][1] != 0)
		switch (argv[1][1]) {
		case 'c':
			pcode_file = get_opt(&argc, &argv);
			break;
		default:
			usage();
			break;
		}

	init_op_tab();
	q = q_load(argc > 1 ? argv[1]: "test.txt", err_str);
	if (q == NULL)
		printf("%s\n", err_str);
	else if (pcode_file != NULL)
		q_save(pcode_file, q, err_str);

	return (0);
}
