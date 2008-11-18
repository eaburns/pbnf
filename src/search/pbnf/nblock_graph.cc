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
#include <math.h>

#include <iostream>
#include <list>
#include <map>
#include <vector>

#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "../projection.h"
#include "nblock.h"
#include "nblock_graph.h"

using namespace std;
using namespace PBNF;

/**
 * Create a new NBlock graph.
 * \param p The projection function.
 */
NBlockGraph::NBlockGraph(const Projection *p, const State *initial)
{
	map<unsigned int, NBlock *>::iterator iter;
	unsigned int init_nblock = p->project(initial);

	num_sigma_zero = num_nblocks = p->get_num_nblocks();
	assert(init_nblock < num_nblocks);

	for (unsigned int i = 0; i < num_nblocks; i += 1) {
		NBlock *n = new NBlock(i);
		if (i == init_nblock) {
			n->open.add(initial);
			free_list.add(n);
		}

		blocks[i] = n;
	}

	// Now connect the graph.
	for (iter = blocks.begin(); iter != blocks.end(); iter++) {
		NBlock *n = iter->second;
		vector<unsigned int>::iterator i, j;
		vector<unsigned int> preds = p->get_predecessors(n->id);
		vector<unsigned int> succs = p->get_successors(n->id);

		// predecessors, successors and the predecessors of the successors.
		vector<unsigned int> interferes = preds;
		for (i = succs.begin(); i != succs.end(); i++) {
			interferes.push_back(*i);
			vector<unsigned int> spreds = p->get_predecessors(*i);
			for (j = spreds.begin(); j != spreds.end(); j++) {
				interferes.push_back(*j);
			}
		}

		for (i = preds.begin(); i != preds.end(); i++)
			if (*i != n->id)
				n->preds.insert(blocks[*i]);

		for (i = succs.begin(); i != succs.end(); i++)
			if (*i != n->id)
				n->succs.insert(blocks[*i]);

		for (i = interferes.begin(); i != interferes.end(); i++)
			if (*i != n->id)
				n->interferes.insert(blocks[*i]);
	}

	done = false;

	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);

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
 * nblock.  The next nblock is the one with the minimum f-value.
 *
 * \note This call will block if there are currently no free nblocks.
 * \param finished If non-NULL, the finished nblock will be released
 *        into the next level's free_list.
 * \param check_scope Whether or not we should test NBlocks in our
 *                    scope to see if they are better.
 * \return The next NBlock to expand or NULL if there is nothing left
 *         to do.
 */
NBlock *NBlockGraph::next_nblock(NBlock *finished, bool check_scope)
{
	NBlock *n = NULL;
	NBlock *best_scope = NULL;

	pthread_mutex_lock(&mutex);

	if (finished) {		// Release an NBlock
		if (check_scope)
			best_scope = __best_in_scope(finished);
		double scope_f = INFINITY;
		if (best_scope)
			scope_f = best_scope->open.get_best_f();

		if (finished->sigma != 0) {
			cerr << "A proc had an NBlock with sigma != 0" << endl;
			finished->print(cerr);
			cerr << endl << endl << endl;
			__print(cerr);
		}
		assert(finished->sigma == 0);

		if (!free_list.empty() && !finished->open.empty()) {
			// If there is not a free NBlock or an NBlock
			// in the interference scope that is better
			// than the one being freed, just search the
			// previous one more.
			double cur_f = finished->open.get_best_f();
			double new_f = free_list.best_f();
			if (cur_f <= new_f && cur_f < scope_f) {
				n = finished;
				goto out;
			}
		}

		nblocks_assigned -= 1;

		if (!finished->open.empty()) {
			free_list.add(finished);
			pthread_cond_broadcast(&cond);
		}

		if (scope_f < free_list.best_f()
		    && (!best_scope || best_scope->sigma > 0))
			best_scope->waitingfor.insert(pthread_self());

		update_scope_sigmas(finished->id, -1);

		// short-cut: if the best block in our scope was freed
		// when we released our block, NULL-out the best_scope
		// variable so we don't need to check the waitingfor
		// set later.
		if (best_scope && best_scope->waitingfor.empty())
			best_scope = NULL;

		if (free_list.empty() && num_sigma_zero == num_nblocks) {
			__set_done();
//			__print(cerr);
			goto out;
		}

	}

	while ((free_list.empty()
		|| (best_scope && (best_scope->waitingfor.find(pthread_self())
				   != best_scope->waitingfor.end())))
	       && !done)
		pthread_cond_wait(&cond, &mutex);

	if (done)
		goto out;

	n = free_list.take();
	nblocks_assigned += 1;
	if (nblocks_assigned > nblocks_assigned_max)
		nblocks_assigned_max = nblocks_assigned;
	update_scope_sigmas(n->id, 1);

/*
	for (set<NBlock *>::iterator iter = n->interferes.begin();
	     iter != n->interferes.end();
	     iter++)
		assert((*iter)->sigma > 0);
*/
out:
	pthread_mutex_unlock(&mutex);

	return n;
}

/**
 * Get the cost of the best NBlock that is interfered with, if there
 * is one.
 */
double NBlockGraph::best_in_scope(NBlock *b)
{
	double ret = INFINITY;

	pthread_mutex_lock(&mutex);
	NBlock *s = __best_in_scope(b);
	if (s)
		ret = s->open.get_best_f();
	pthread_mutex_unlock(&mutex);

	return ret;
}

/**
 * Get the best NBlock that is interfered with, if there is one.
 */
NBlock *NBlockGraph::__best_in_scope(NBlock *b)
{
	NBlock *best_b = NULL;
	double best_f = INFINITY;
	map<unsigned int, NBlock*>::iterator i;

	for (i = blocks.begin(); i != blocks.end(); i++) {
		NBlock *b = i->second;
		if (b->open.empty())
			continue;
		if (!best_b || b->open.get_best_f() < best_f) {
			best_f = b->open.get_best_f();
			best_b = b;
		}
	}

	return best_b;
}

/**
 * We won't release block b, so if there are processess waiting on it,
 * the wake them all up.
 */
void NBlockGraph::wont_release(NBlock *b)
{
	set<NBlock *>::iterator iter;
	bool wake = false;

	pthread_mutex_lock(&mutex);

	for (iter = b->interferes.begin();
	     iter != b->interferes.end();
	     iter++) {
		if (!(*iter)->waitingfor.empty()) {
			(*iter)->waitingfor.clear();
			wake = true;
		}
	}

	pthread_cond_broadcast(&cond);
	pthread_mutex_unlock(&mutex);
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


	o << "Number of NBlocks: " << num_nblocks << endl;
	o << "Number of NBlocks with sigma zero: " << num_sigma_zero << endl;
	o << "--------------------" << endl;
	o << "Free Blocks:" << endl;
	free_list.print(o);
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
void NBlockGraph::update_sigma(NBlock *yblk, int delta)
{
	if (yblk->sigma == 0) {
		assert(delta > 0);
		if (!yblk->open.empty())
			free_list.remove(yblk);
		num_sigma_zero -= 1;
	}

	yblk->sigma += delta;

	if (yblk->sigma == 0) {
		if (!yblk->open.empty()) {
			free_list.add(yblk);
			yblk->waitingfor.clear();
			pthread_cond_broadcast(&cond);
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
	set<NBlock *>::iterator iter;

	assert(blocks[y]->sigma == 0);

	/*
	  \A y' \in predecessors(y) /\ y' /= y,
	  \sigma(y') <- \sigma(y') +- 1

	  \A y' \in successors(y),
	  \A y'' \in predecessors(y'), /\ y'' /= y,
	  \sigma(y'') <- \sigma(y'') +- 1
	*/

	for (iter = blocks[y]->interferes.begin();
	     iter != blocks[y]->interferes.end();
	     iter++) {
		update_sigma(*iter, delta);
	}
}

/**
 * Get the f-value of the next best NBlock.
 */
float NBlockGraph::next_nblock_f_value(void)
{
	float val;

	pthread_mutex_lock(&mutex);
	val = free_list.best_f();
	pthread_mutex_unlock(&mutex);

	return val;
}

/**
 * Sets the done flag with out taking the lock.
 */
void NBlockGraph::__set_done(void)
{
	done = true;
	pthread_cond_broadcast(&cond);
}

/**
 * Sets the done flag.
 */
void NBlockGraph::set_done(void)
{
	pthread_mutex_lock(&mutex);
	__set_done();
	pthread_mutex_unlock(&mutex);
}
