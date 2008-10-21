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

#include "nblock_graph.h"

using namespace std;

/**
 * Create a new NBlock structure.
 */
NBlockGraph::NBlock::NBlock(void)
{
	sigma = 0;
	cur_open = &open_a;
	next_open = &open_b;
}

/**
 * Create a new NBlock graph.
 * \param p The projection function.
 */
NBlockGraph::NBlockGraph(Projection *p)
{
	for (unsigned int i = 0; i < p->get_num_nblocks(); i += 1) {
		NBlock *n = new NBlock;
		blocks[i] = n;
		free_list.push(i);
	}
}

/**
 * Destroy an NBlock graph.
 */
NBlockGraph::~NBlockGraph()
{
	map<unsigned int, NBlock *>::iterator iter;

	for (iter = blocks.begin(); iter != blocks.end(); iter++)
		delete iter->second;
}

#if 0
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
#endif	// 0
