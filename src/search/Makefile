CXX=g++
CXXFLAGS=-g -Wall -Werror -pipe #-lpthread

SRC= \
	state.cc \
	search_domain.cc \
	open_list.cc \
	closed_list.cc \
	search.cc \
	a_star.cc \
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
