/* -*- mode:linux -*- */
/**
 * \file nblock_graph.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include <vector>
#include <map>

#include <assert.h>

#include "nblock.h"
#include "nblock_free_list.h"
#include "nblock_graph.h"

using namespace std;

/**
 * Create a new NBlock graph.
 */
NBlockGraph::NBlockGraph(NBlockFactory *fact, NBlockFreeList *f, Projection *p)
	: free_list(f)
{
	for (unsigned int i = 0; i < p->get_num_nblocks(); i += 1) {
		blocks.push_back(fact->new_nblock(i));
		sigmas.push_back(0);
		preds[i] = p->get_predecessors(i);
		succs[i] = p->get_successors(i);
	}
}

NBlockGraph::~NBlockGraph() {}

/**
 * Get a pointer to the next free nblock.
 */
NBlock *NBlockGraph::next_free_nblock(void)
{
	NBlock *b = free_list->next();

	free_list->remove(b);

	return b;
}

void NBlockGraph::update_sigma(unsigned int y, int delta)
{
	if (sigmas[y] == 0) {	// block is no longer free
		assert(delta > 0);
		free_list->remove(blocks[y]);
	}

	sigmas[y] += delta;

	if (sigmas[y] == 0)	// block is now free
		free_list->add(blocks[y]);
}

/**
 * Update the sigmas by delta for all of the predecessors of y and all
 * of the predecessors of the successors of y.
 */
void NBlockGraph::update_scope_sigmas(unsigned int y, int delta)
{
	vector<unsigned int>::iterator iter;
	vector<unsigned int>::iterator iter1;

	assert(sigmas.at(y) == 0);

	/*
	  \A y' \in predecessors(y) /\ y' /= y,
	  \sigma(y') <- \sigma(y') +- 1
	*/
	for (iter = preds[y].begin(); iter != preds[y].end(); iter++) {
		unsigned int yp = *iter;
		if (yp != y)
			update_sigma(yp, delta);

	}

	/*
	  \A y' \in successors(y),
	  \A y'' \in predecessors(y'), /\ y'' /= y,
	  \sigma(y'') <- \sigma(y'') +- 1
	 */
	for (iter = succs[y].begin(); iter != succs[y].end(); iter++) {
		unsigned int yp = *iter;
		for (iter1 = preds[yp].begin();
		     iter1 != preds[yp].end();
		     iter1++) {
			unsigned int ypp = *iter1;
			if (ypp != y)
				update_sigma(ypp, delta);
		}
	}
}

/**
 * A processor acquires an NBlock.
 */
void NBlockGraph::acquire_nblock(unsigned int y)
{
	update_scope_sigmas(y, 1);
}

/**
 * A processor releases an NBlock.
 */
void NBlockGraph::release_nblock(unsigned int y)
{
	update_scope_sigmas(y, -1);
}
