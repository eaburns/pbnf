CXX=g++

# Comment this out for faster, more memory efficient code.
IMAGES=-DENABLE_IMAGES


CXXFLAGS=-g -Wall -Werror -Wnon-virtual-dtor -pedantic -pipe $(IMAGES) #-lpthread

SRC= \
	state.cc \
	search_domain.cc \
	open_list.cc \
	pq_open_list.cc \
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
	grid/manhattan_dist.cc \
	grid/grid_state.cc \
	grid/grid_world.cc \
	psdd/nblock.cc \
	#kbfs.cc \

OBJ=$(SRC:.cc=.o)

all: test

test: $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) -o test $(OBJ) main.cc

depend:
	rm -f .depend
	touch .depend
	(find . -name \*.cc; find . -name \*.h) | xargs makedepend -f.depend -Y
	rm -f .depend.bak

clean:
	find . -name \*.o -exec rm -f '{}' \;
	rm -f test

-include .depend
