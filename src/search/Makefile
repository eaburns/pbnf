CXX=g++

# Comment this out for faster, more memory efficient code.
IMAGES=-DENABLE_IMAGES

CXXFLAGS=-g -Wall -Werror -pipe $(IMAGES) #-lpthread

SRC= \
	state.cc \
	search_domain.cc \
	pq_open_list.cc \
	synch_pq_olist.cc \
	closed_list.cc \
	search.cc \
	a_star.cc \
	cost_bound_dfs.cc \
	ida_star.cc \
	grid/manhattan_dist.cc \
	grid/grid_state.cc \
	grid/grid_world.cc \
	#kbfs.cc \

OBJ=$(SRC:.cc=.o)

all: test

test: $(OBJ) main.cc
	$(CXX) $(CXXFLAGS) -o test $(OBJ) main.cc

clean:
	find . -name \*.o -exec rm -f '{}' \;
	rm -f test
