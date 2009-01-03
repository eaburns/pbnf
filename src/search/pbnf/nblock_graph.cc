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
#include <errno.h>

#include <limits>
#include <iostream>
#include <list>
#include <map>
#include <vector>

#include "../closed_list.h"
#include "../pq_open_list.h"
#include "../open_list.h"
#include "../projection.h"
#include "../pbnf_search.h"
#include "nblock.h"
#include "nblock_graph.h"

using namespace std;
using namespace PBNF;

void NBlockGraph::cpp_is_a_bad_language(const Projection *p, State *initial)
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
 * Create a new NBlock graph.
 * \param p The projection function.
 */
NBlockGraph::NBlockGraph(const Projection *p, State *initial)
{
	cpp_is_a_bad_language(p, initial);
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
 * \param trylock Set to true if a trylock should be attempted instead
 *                of a lock.
 * \return The next NBlock to expand or NULL if there is nothing left
 *         to do.
 */
NBlock *NBlockGraph::next_nblock(NBlock *finished, bool trylock, bool dynamic_m)
{
	NBlock *n = NULL;

	// Take the lock, but if someone else already has it, just
	// keep going.
	if (trylock && finished && !finished->open.empty()) {
		if (pthread_mutex_trylock(&mutex) == EBUSY){
			if(dynamic_m){
				PBNFSearch::inc_m();
			}
			return finished;
		}
		else if(dynamic_m){
			PBNFSearch::dec_m();
		}
	} else if(!dynamic_m || pthread_mutex_trylock(&mutex) == EBUSY){
		if(dynamic_m){
			PBNFSearch::inc_m();
		}
		pthread_mutex_lock(&mutex);
	}
	else if(dynamic_m){
		PBNFSearch::dec_m();
	}
	

	if (finished) {		// Release an NBlock
		if (finished->sigma != 0) {
			cerr << "A proc had an NBlock with sigma != 0" << endl;
			finished->print(cerr);
			cerr << endl << endl << endl;
			__print(cerr);
		}
		assert(finished->sigma == 0);

		if (!finished->open.empty()) {
			double cur_f = finished->open.get_best_f();
			double new_f;
			if (free_list.empty())
				new_f = numeric_limits<float>::infinity();
			else
				new_f = free_list.best_f();
			if (cur_f <= new_f) {
				n = finished;
				goto out;
			}
		}

		nblocks_assigned -= 1;

		if (is_free(finished)) {
			free_list.add(finished);
			pthread_cond_broadcast(&cond);
		}
		finished->inuse = false;
		update_scope_sigmas(finished->id, -1);

		if (free_list.empty() && num_sigma_zero == num_nblocks) {
			__set_done();
//			__print(cerr);
			goto out;
		}

	}

	while (!done && free_list.empty())
		pthread_cond_wait(&cond, &mutex);

	if (done)
		goto out;

	n = free_list.take();
	nblocks_assigned += 1;
	if (nblocks_assigned > nblocks_assigned_max)
		nblocks_assigned_max = nblocks_assigned;
	n->inuse = true;
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
 * Get the best NBlock in the interference scope of b which is not free.
 */
NBlock *NBlockGraph::best_in_scope(NBlock *b)
{
	NBlock *best_b = NULL;
	double best_f = numeric_limits<float>::infinity();
	map<unsigned int, NBlock*>::iterator i;

//	pthread_mutex_lock(&mutex);

	for (i = blocks.begin(); i != blocks.end(); i++) {
		NBlock *b = i->second;
		if (b->open.empty())
			continue;
		if (!best_b || b->open.get_best_f() < best_f) {
			best_f = b->open.get_best_f();
			best_b = b;
		}
	}

//	pthread_mutex_unlock(&mutex);

	// best_b => best_f != numeric_limits<float>::infinity();
	assert(best_f != numeric_limits<float>::infinity() || !best_b);

	return best_b;
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
		if ((*iter)->sigma == 0) {
			assert(delta > 0);
			if (is_free(*iter))
				free_list.remove(*iter);
			num_sigma_zero -= 1;
		}
		(*iter)->sigma += delta;
		if ((*iter)->sigma == 0) {
			if ((*iter)->hot)
				set_cold(*iter);
			if (is_free(*iter)) {
				free_list.add(*iter);
				pthread_cond_broadcast(&cond);
			}
			num_sigma_zero += 1;
		}
	}
}

/**
 * Get the f-value of the next best NBlock.
 */
float NBlockGraph::next_nblock_f_value(void)
{
	// this is atomic
	return free_list.best_f();
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

/**
 * Test if an NBlock is free.
 */
bool NBlockGraph::is_free(NBlock *b)
{
	return !b->inuse
		&& b->sigma == 0
		&& b->sigma_hot == 0
		&& !b->open.empty();
}

/**
 * Mark an NBlock as hot, we want this one.
 */
void NBlockGraph::set_hot(NBlock *b, bool dynamic_m)
{
	set<NBlock*>::iterator i;
	float f = b->open.get_best_f();

	if(!dynamic_m || pthread_mutex_trylock(&mutex) == EBUSY){
		if(dynamic_m){
			PBNFSearch::inc_m();
		}
		pthread_mutex_lock(&mutex);
	}
	else{
		if(dynamic_m){
			PBNFSearch::dec_m();
		}
	}
	if (!b->hot && b->sigma > 0) {
		for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
			assert(b != *i);
			if ((*i)->hot && (*i)->open.get_best_f() < f)
				goto out;
		}

		b->hot = true;
		for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
			assert(b != *i);
			if (is_free(*i))
				free_list.remove(*i);
			if ((*i)->hot)
				set_cold(*i);
			(*i)->sigma_hot += 1;
		}
	}
out:
	pthread_mutex_unlock(&mutex);
}

/**
 * Mark an NBlock as cold.  The mutex must be held *before* this
 * function is called.n
 */
void NBlockGraph::set_cold(NBlock *b)
{
	set<NBlock*>::iterator i;

	b->hot = false;
	for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
		assert(b != *i);
		(*i)->sigma_hot -= 1;
		if (is_free(*i)) {
			free_list.add(*i);
			pthread_cond_broadcast(&cond);
		}
	}
}

/**
 * We won't release block b, so set all hot blocks in its interference
 * scope back to cold.
 */
void NBlockGraph::wont_release(NBlock *b, bool dynamic_m)
{
	set<NBlock *>::iterator iter;

	if(!dynamic_m || pthread_mutex_trylock(&mutex) == EBUSY){
		if(dynamic_m){
			PBNFSearch::inc_m();
		}
		pthread_mutex_lock(&mutex);
	}
	else if(dynamic_m){
		PBNFSearch::dec_m();
	}

	for (iter = b->interferes.begin();
	     iter != b->interferes.end();
	     iter++) {
		if ((*iter)->hot)
			set_cold(*iter);
	}

	pthread_mutex_unlock(&mutex);
}
