# Copyright (c) 2006, 2007 by Sergey Lyubka
# All rights reserved
#
# $Id$

SRCS=	q.c
PROG=	q
CFLAGS=	-W -Wall -g -pedantic -ansi -D_BSD_SOURCE $(COPT)

all:	$(PROG)

$(PROG): $(HDRS) $(SRCS)
	$(CC) $(CFLAGS) $(SRCS) -o $@

clean:
	rm -f *.o $(PROG) *core
