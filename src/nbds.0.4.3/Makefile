# MARCH=$(shell uname -m)

# # These are all really the same thing here
# ifeq ($(MARCH), i686)
# MARCH=i386
# endif
# ifeq ($(MARCH), i586)
# MARCH=i386
# endif

CC=gcc
CFLAGS=-Wall -Werror -std=gnu99 -Iinclude -DNDEBUG -O3
SRC= 				\
	runtime/runtime.c	\
	runtime/rcu.c		\
	runtime/lwt.c		\
	runtime/mem.c		\
	datatype/nstring.c	\
	map/map.c		\
	map/list.c		\
	map/skiplist.c		\
	map/hashtable.c

OBJ=$(SRC:.c=.o)

LIBNBDS=libnbds-$(MARCH).a

all: $(LIBNBDS)

$(LIBNBDS): $(OBJ)
	$(AR) crs $@ $^


clean:
	find . -name \*.o -exec rm '{}' \;
	rm -f $(LIBNBDS)
