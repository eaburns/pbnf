/* -*- mode:linux -*- */
/**
 * \file nblock_graph.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include <assert.h>
#include <pthread.h>

#include <list>
#include <map>
#include <vector>

#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "projection.h"
#include "nblock.h"
#include "nblock_graph.h"

using namespace std;

/**
 * Create a new NBlock graph.
 * \param p The projection function.
 */
NBlockGraph::NBlockGraph(Projection *p, const State *initial)
{
	unsigned int init_nblock = p->project(initial);
	cur_free_list = &free_list_a;
	next_free_list = &free_list_b;

	num_sigma_zero = num_nblocks = p->get_num_nblocks();
	assert(init_nblock < num_nblocks);

	for (unsigned int i = 0; i < num_nblocks; i += 1) {
		NBlock *n = new NBlock(i, p->get_predecessors(i),
				       p->get_successors(i));
		if (i == init_nblock) {
			n->cur_open->add(initial);
			cur_free_list->push_back(n);
		}

		blocks[i] = n;
	}

	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
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

/**
 * Get the next nblock for expansion, possibly release a finished
 * nblock.
 * \note This call will block if there are currently no free nblocks.
 * \param finished If non-NULL, the finished nblock will be released
 *        into the next level's free_list.
 * \return The next NBlock to expand or NULL if there is nothing left
 *         to do.
 */
NBlock *NBlockGraph::next_nblock(NBlock *finished)
{
	NBlock *n;

	pthread_mutex_lock(&mutex);

	if (finished) {		// Release an NBlock
		assert(finished->sigma == 0);
		update_scope_sigmas(finished->id, -1);
		next_free_list->push_back(finished);

		if (cur_free_list->size() == 0 && num_sigma_zero == num_nblocks) {
			// If there are no NBlocks that are currently
			// free with nodes on them, and all of the
			// NBlocks have sigma values of zero:
			// Switch to the next iteration
			list<NBlock *> *tmp;
			map<unsigned int, NBlock *>::iterator iter;

			// Swap the NBlock free_lists.
			tmp = cur_free_list;
			cur_free_list = next_free_list;
			next_free_list = tmp;

			// Switch the open lists on all of the NBlocks.
			for (iter = blocks.begin(); iter != blocks.end(); iter++)
				iter->second->next_iteration();

			// Wake up everyone...
			pthread_cond_broadcast(&cond);
		}
	}

	while (cur_free_list->empty())
		pthread_cond_wait(&cond, &mutex);

	n = cur_free_list->front();
	cur_free_list->pop_front();

	pthread_mutex_unlock(&mutex);

	return n;
}


/**
 * Update the sigma value of a block, add it to the freelist if need
 * be, or remove it from the freelist.
 */
void NBlockGraph::update_sigma(unsigned int y, int delta)
{
	NBlock *yblk = blocks[y];

	if (yblk->sigma == 0) {
		assert(delta > 0);
		if (!yblk->cur_open->empty())
			cur_free_list->remove(yblk);
		num_sigma_zero -= 1;
	}

	yblk->sigma += delta;

	if (yblk->sigma == 0) {
		if (!yblk->cur_open->empty()) {
			cur_free_list->push_back(yblk);
			pthread_cond_signal(&cond);
		}

		num_sigma_zero += 1;
	}
}

/**
 * Update the sigmas by delta for all of the predecessors of y and all
 * of the predecessors of the successors of y.
 */
void NBlockGraph::update_scope_sigmas(unsigned int y, int delta)
{
	NBlock *b;
	vector<unsigned int>::iterator iter;
	vector<unsigned int>::iterator iter1;

	assert(blocks[y]->sigma == 0);

	/*
	  \A y' \in predecessors(y) /\ y' /= y,
	  \sigma(y') <- \sigma(y') +- 1
	*/
	b = blocks[y];
	for (iter = b->preds.begin(); iter != b->preds.end(); iter++) {
		unsigned int yp = *iter;
		if (yp != y)
			update_sigma(yp, delta);

	}

	/*
	  \A y' \in successors(y),
	  \A y'' \in predecessors(y'), /\ y'' /= y,
	  \sigma(y'') <- \sigma(y'') +- 1
	 */
	for (iter = b->succs.begin(); iter != b->succs.end(); iter++) {
		unsigned int yp = *iter;
		NBlock *yblk = blocks[yp];
		for (iter1 = yblk->preds.begin();
		     iter1 != yblk->preds.end();
		     iter1++) {
			unsigned int ypp = *iter1;
			if (ypp != y)
				update_sigma(ypp, delta);
		}
	}
}
