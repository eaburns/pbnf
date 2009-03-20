MARCH=$(shell uname -m)

OBJDIR=objs.$(MARCH)

SRC= \
	get_search.cc \
	state.cc \
	search_domain.cc \
	open_list.cc \
	queue_open_list.cc \
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
	div_merge_project.cc \
	util/eps.cc \
	util/thread.cc \
	util/completion_counter.cc \
	util/timer.cc \
	util/timeout.cc \
	util/atomic_float.cc \
	util/cumulative_ave.cc \
	grid/grid_state.cc \
	grid/grid_world.cc \
	tiles/tiles_state.cc \
	tiles/tiles.cc \
	psdd/nblock.cc \
	psdd/nblock_graph.cc \
	psdd_search.cc \
	wbfpsdd/nblock.cc \
	wbfpsdd/nblock_graph.cc \
	wbfpsdd_search.cc \
	bfpsdd_search.cc \
	idpsdd_search.cc \
	dynamic_bounded_psdd.cc \
	wpbnf/nblock.cc \
	wpbnf/nblock_graph.cc \
	wpbnf/nblock_free_list.cc \
	wpbnf_search.cc \
	pbnf/nblock.cc \
	pbnf/nblock_graph.cc \
	pbnf/nblock_free_list.cc \
	pbnf_search.cc \
	kbfs.cc \
	pastar.cc \
	prastar.cc \
	wprastar.cc

OBJ=$(addprefix $(OBJDIR)/, $(SRC:.cc=.o))

ifeq ($(MARCH), sparc64)
FLAGS+=-mcpu=v9
OBJ+=$(OBJDIR)/util/sparc64_atomic_asm.o
OBJ+=$(OBJDIR)/util/sparc64_atomic_int.o
else ifeq ($(MARCH), sun4v)
OBJ+=$(OBJDIR)/util/sparc64_atomic_int.o
else ifeq ($(MARCH), i386)
OBJ+=$(OBJDIR)/util/i386_atomic_int.o
OBJ+=$(OBJDIR)/util/cmpxchg_i386.o
else ifeq ($(MARCH), i686)
OBJ+=$(OBJDIR)/util/i386_atomic_int.o
OBJ+=$(OBJDIR)/util/cmpxchg_i386.o
else ifeq ($(MARCH), x86_64)
OBJ+=$(OBJDIR)/util/x86_64_atomic_int.o
CXXFLAGS+=-D_64_BIT_LONG
else
$(error Unknown machine type)
endif

############################################################
# Compiler specific flags
ifeq ($(MARCH), sun4v) # Sun compilers
CC=cc
CXX=CC
#DEBUG=-g -xO0   # use the dbx debugger
DEBUG+=-DNDEBUG
FLAGS+=-mt -errwarn=%all $(DEBUG)
ASFLAGS+=-xc99=%none
CFLAGS+=-xc99=%none
LDFLAGS+=-lpthread -lmtmalloc
else                   # GNU compilers
PROFILE+=
#PROFILE+=-pg
DEBUG+=-O3 -DNDEBUG
#DEBUG+=-g -O0 -fno-default-inline -fno-implicit-inline-templates -fno-implement-inlines
FLAGS+=-Wall -Werror -pipe $(DEBUG) $(PROFILE)
CXXFLAGS+=-Wnon-virtual-dtor 
LDFLAGS+=-lpthread $(PROFILE)
#LDFLAGS+=-lpthread $(PROFILE) -ltcmalloc
#LDFLAGS+=-L /home/rai/eaburns/tmp/lib -ljemalloc_mt -lpthread $(PROFILE)
endif
############################################################

#FLAGS+=-DENABLE_IMAGES

CFLAGS+=$(FLAGS)
ASFLAGS+=$(FLAGS)
CXXFLAGS+=$(FLAGS)

PROGS=$(addsuffix .$(MARCH), \
	grid_search \
	tiles_search \
	thread_test \
	atomic_int_test \
	psdd_nblock_graph_test \
	pbnf_nblock_graph_test \
	tiles_hash_test \
	tiles_read_test \
	atomic_float_test \
	pq_test \
	one_tile_project_test \
	two_tile_project_test)

all: objdirs $(PROGS)

grid_search.$(MARCH): $(OBJ) grid_search.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) grid_search.cc

tiles_search.$(MARCH): $(OBJ) tiles_search.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles_search.cc

thread_test.$(MARCH): $(OBJ) util/thread_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) util/thread_test.cc

atomic_int_test.$(MARCH): $(OBJ) util/atomic_int_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) util/atomic_int_test.cc

psdd_nblock_graph_test.$(MARCH): $(OBJ) psdd/nblock_graph_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) psdd/nblock_graph_test.cc

pbnf_nblock_graph_test.$(MARCH): $(OBJ) pbnf/nblock_graph_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) pbnf/nblock_graph_test.cc

tiles_hash_test.$(MARCH): $(OBJ) tiles/tiles_hash_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles/tiles_hash_test.cc

tiles_read_test.$(MARCH): $(OBJ) tiles/tiles_read_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles/tiles_read_test.cc

atomic_float_test.$(MARCH): $(OBJ) util/atomic_float_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) util/atomic_float_test.cc

div_merge_project_test.$(MARCH): $(OBJ) tiles/div_merge_project_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles/div_merge_project_test.cc

one_tile_project_test.$(MARCH): $(OBJ) tiles/one_tile_project_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles/one_tile_project_test.cc

two_tile_project_test.$(MARCH): $(OBJ) tiles/two_tile_project_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) tiles/two_tile_project_test.cc

pq_open_list_test.$(MARCH): $(OBJ) pq_open_list_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) pq_open_list_test.cc

pq_test.$(MARCH): $(OBJ) util/pq_test.cc
	$(CXX) $(CXXFLAGS) $(LDFLAGS) -o $@ $(OBJ) util/pq_test.cc

create_bins: grid_search.$(MARCH) tiles_search.$(MARCH)
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo Is debugging turned off?
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo
	@echo
	cp grid_search.$(MARCH) grid_search.$(MARCH).bin
	cp tiles_search.$(MARCH) tiles_search.$(MARCH).bin

$(OBJDIR)/%.o: %.cc
	$(COMPILE.cc) $< -o $@

$(OBJDIR)/%.o: %.c
	$(COMPILE.c) $< -o $@

$(OBJDIR)/%.o: %.S
	$(COMPILE.S) $< -o $@

.PHONY: depend
depend:
	rm -f .depend
	touch .depend
	(find . -name \*.cc -printf "%f\n"; find . -name \*.h -printf "%f\n") | xargs makedepend -f.depend -Y -p$(OBJDIR)/
	rm -f .depend.bak

.PHONY: objdirs
objdirs:
	$(foreach file, $(SRC), $(shell test -d $(OBJDIR)/$(dir $(file)) || mkdir -p $(OBJDIR)/$(dir $(file))))

.PHONY: clean
 clean:
	rm -fr $(OBJDIR)
	rm -f $(PROGS)

-include .depend
