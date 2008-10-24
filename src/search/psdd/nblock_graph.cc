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

#include <iostream>
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

	num_sigma_zero = num_nblocks = p->get_num_nblocks();
	assert(init_nblock < num_nblocks);

	for (unsigned int i = 0; i < num_nblocks; i += 1) {
		NBlock *n = new NBlock(i, p->get_predecessors(i),
				       p->get_successors(i));
		if (i == init_nblock) {
			n->cur_open->add(initial);
			free_list.push_back(n);
		}

		blocks[i] = n;
	}

	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
	path_found = false;

	nblocks_assigned = 0;
	nblocks_assigned_max = 0;
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
	NBlock *n = NULL;

	pthread_mutex_lock(&mutex);

	if (finished) {		// Release an NBlock
		if (finished->sigma != 0) {
			cerr << "A proc had an NBlock with sigma != 0" << endl;
			finished->print(cerr);
			cerr << endl << endl << endl;
			__print(cerr);
		}
		assert(finished->sigma == 0);

		nblocks_assigned -= 1;
		update_scope_sigmas(finished->id, -1);

		if (free_list.size() == 0 && num_sigma_zero == num_nblocks) {
			// If there are no NBlocks that are currently
			// free with nodes on them, and all of the
			// NBlocks have sigma values of zero:
			// Switch to the next iteration
			map<unsigned int, NBlock *>::iterator iter;

			// Switch the open lists on all of the NBlocks.
			for (iter = blocks.begin(); iter != blocks.end(); iter++) {
				iter->second->next_iteration();
				if (!iter->second->cur_open->empty())
					free_list.push_back(iter->second);
			}

			if (free_list.empty())
				goto out;

			// Wake up everyone...
			pthread_cond_broadcast(&cond);
		}
	}

	while (free_list.empty() && !path_found)
		pthread_cond_wait(&cond, &mutex);

	if (path_found)
		goto out;

	n = free_list.front();
	free_list.pop_front();
	nblocks_assigned += 1;
	if (nblocks_assigned > nblocks_assigned_max)
		nblocks_assigned_max = nblocks_assigned;
	update_scope_sigmas(n->id, 1);
out:
	pthread_mutex_unlock(&mutex);

	return n;
}


/**
 * Get the NBlock given by the hash value.
 * This shouldn't be called unless the calling thread has this block
 * assigned to it.
 */
NBlock *NBlockGraph::get_nblock(unsigned int hash)
{
	return blocks[hash];
}


/**
 * Signal anyone else that is waiting that a path has been found and
 * there is no need to get a new NBlock.
 */
void NBlockGraph::set_path_found(void)
{
	pthread_mutex_lock(&mutex);
	path_found = true;
	pthread_cond_broadcast(&cond);
	pthread_mutex_unlock(&mutex);
}


/**
 * Get the statistics on the maximum number of NBlocks assigned at one time.
 */
unsigned int NBlockGraph::get_max_assigned_nblocks(void) const
{

	return nblocks_assigned_max;
}


/**
 * Print an NBlock, but don't take the lock.
 */
void NBlockGraph::__print(ostream &o)
{
	map<unsigned int, NBlock *>::iterator biter;
	list<NBlock *>::iterator fiter;

	o << "Number of NBlocks: " << num_nblocks << endl;
	o << "Number of NBlocks with sigma zero: " << num_sigma_zero << endl;
	o << "--------------------" << endl;
	o << "Current Free Blocks:" << endl;
	for (fiter = free_list.begin();
	     fiter != free_list.end();
	     fiter++)
		(*fiter)->print(o);
	o << "--------------------" << endl;

	o << "All Blocks:" << endl;
	for (biter = blocks.begin(); biter != blocks.end(); biter++)
		biter->second->print(o);
}

/**
 * Print an NBlockGraph to the given stream.
 */
void NBlockGraph::print(ostream &o)
{
	pthread_mutex_lock(&mutex);
	__print(o);
	pthread_mutex_unlock(&mutex);
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
			free_list.remove(yblk);
		num_sigma_zero -= 1;
	}

	yblk->sigma += delta;

	if (yblk->sigma == 0) {
		if (!yblk->cur_open->empty()) {
			free_list.push_back(yblk);
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
