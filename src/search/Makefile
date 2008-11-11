CXX=g++

MARCH=$(shell uname -m)

# profiler flags
#PROF_FLAGS=-pg
PROF_FLAGS=

# C/C++ basic compilation flags
FLAGS=-g -Wall -pipe -O0 $(PROF_FLAGS)

# Comment this out for faster, more memory efficient code.
#FLAGS+=-DENABLE_IMAGES

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
	multi_a_star.cc \
	breadth_first_search.cc \
	cost_bound_dfs.cc \
	ida_star.cc \
	heuristic.cc \
	h_zero.cc \
	weighted_heuristic.cc \
	projection.cc \
	util/eps.cc \
	util/thread.cc \
	util/completion_counter.cc \
	util/timer.cc \
	util/atomic_float.cc \
	grid/grid_state.cc \
	grid/grid_world.cc \
	tiles/tiles_state.cc \
	tiles/tiles.cc \
	psdd/nblock.cc \
	psdd/nblock_graph.cc \
	psdd_search.cc \
	dynamic_bounded_psdd.cc \
	pbnf/nblock.cc \
	pbnf/nblock_graph.cc \
	pbnf/nblock_free_list.cc \
	pbnf_search.cc \
	kbfs.cc \
	pastar.cc \

OBJ=$(SRC:.cc=.o)

ifeq ($(MARCH), sparc64)
FLAGS+=-mcpu=v9
OBJ+=util/sparc64_atomic_asm.o
OBJ+=util/sparc64_atomic_int.o
else ifeq ($(MARCH), i386)
OBJ+=util/i386_atomic_int.o
else ifeq ($(MARCH), x86_64)
OBJ+=util/x86_64_atomic_int.o
else
$(error Unknown machine type)
endif

CFLAGS+=$(FLAGS)
ASFLAGS+=$(FLAGS)
CXXFLAGS+=-Wnon-virtual-dtor $(FLAGS)
LDFLAGS=-lpthread $(PROF_FLAGS)

all: grid_search tiles_search \
     thread_test \
     atomic_int_test \
     psdd_nblock_graph_test \
     pbnf_nblock_graph_test \
     tiles_hash_test \
     tiles_read_test \
     atomic_float_test

grid_search: $(OBJ) grid_search.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o grid_search $(OBJ) grid_search.cc

tiles_search: $(OBJ) tiles_search.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o tiles_search $(OBJ) tiles_search.cc

thread_test: $(OBJ) util/thread_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o thread_test $(OBJ) util/thread_test.cc

atomic_int_test: $(OBJ) util/atomic_int_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o atomic_int_test $(OBJ) util/atomic_int_test.cc

psdd_nblock_graph_test: $(OBJ) psdd/nblock_graph_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o psdd_nblock_graph_test \
	$(OBJ) psdd/nblock_graph_test.cc

pbnf_nblock_graph_test: $(OBJ) pbnf/nblock_graph_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o pbnf_nblock_graph_test \
	$(OBJ) pbnf/nblock_graph_test.cc

tiles_hash_test: $(OBJ) tiles/tiles_hash_test.o
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o tiles_hash_test \
	$(OBJ) tiles/tiles_hash_test.o

tiles_read_test: $(OBJ) tiles/tiles_read_test.o
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o tiles_read_test \
	$(OBJ) tiles/tiles_read_test.o

atomic_float_test: $(OBJ) util/atomic_float_test.o
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o atomic_float_test \
	$(OBJ) util/atomic_float_test.o

depend:
	rm -f .depend
	touch .depend
	(find . -name \*.cc; find . -name \*.h) | xargs makedepend -f.depend -Y
	rm -f .depend.bak

clean:
	find . -name \*.o -exec rm -f '{}' \;
	rm -f grid_search
	rm -f tiles_search
	rm -f thread_test
	rm -f atomic_int_test
	rm -f psdd_nblock_graph_test
	rm -f pbnf_nblock_graph_test
	rm -f tiles_hash_test
	rm -f tiles_read_test
	rm -f atomic_float_

-include .depend
