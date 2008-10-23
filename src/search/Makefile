CXX=g++

MARCH=$(shell uname -m)

# C/C++ basic compilation flags
FLAGS=-g -Wall -pedantic -pipe

# Comment this out for faster, more memory efficient code.
FLAGS+=-DENABLE_IMAGES

SRC= \
	state.cc \
	search_domain.cc \
	open_list.cc \
	pq_open_list.cc \
	queue_open_list.cc \
	synch_pq_olist.cc \
	closed_list.cc \
	synch_closed_list.cc \
	search.cc \
	a_star.cc \
	cost_bound_dfs.cc \
	ida_star.cc \
	heuristic.cc \
	h_zero.cc \
	util/eps.cc \
	util/thread.cc \
	util/$(MARCH)_atomic_int.cc \
	grid/grid_state.cc \
	grid/grid_world.cc \
	psdd/projection.cc \
	psdd/nblock.cc \
	psdd/nblock_graph.cc \
	kbfs.cc \

OBJ=$(SRC:.cc=.o)

ifeq ($(MARCH), sparc64)
FLAGS+=-mcpu=v9

# Sparc64 atomic helper routines
OBJ+=util/sparc64_atomic_asm.o
endif

CFLAGS+=$(FLAGS)
ASFLAGS+=$(FLAGS)
CXXFLAGS+=-Wnon-virtual-dtor $(FLAGS)
LDFLAGS=-lpthread

all: search thread_test atomic_int_test

search: $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o search $(OBJ) main.cc

thread_test: $(OBJ) util/thread_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o thread_test $(OBJ) util/thread_test.cc

atomic_int_test: $(OBJ) util/atomic_int_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o atomic_int_test $(OBJ) util/atomic_int_test.cc

depend:
	rm -f .depend
	touch .depend
	(find . -name \*.cc; find . -name \*.h) | xargs makedepend -f.depend -Y
	rm -f .depend.bak

clean:
	find . -name \*.o -exec rm -f '{}' \;
	rm -f search
	rm -f thread_test
	rm -f atomic_int_test

-include .depend
