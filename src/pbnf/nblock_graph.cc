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

NBlock *NBlockGraph::create_nblock(unsigned int id)
{
	assert(id < project->get_num_nblocks());

	NBlock *n = new NBlock(id);
	vector<unsigned int>::iterator i, j;
	vector<unsigned int> preds = project->get_predecessors(id);
	vector<unsigned int> succs = project->get_successors(id);
	// predecessors, successors and the predecessors of the successors.
	vector<unsigned int> interferes = preds;
	for (i = succs.begin(); i != succs.end(); i++) {
		interferes.push_back(*i);
		vector<unsigned int> spreds = project->get_predecessors(*i);
		for (j = spreds.begin(); j != spreds.end(); j++) {
			interferes.push_back(*j);
		}
	}
	for (i = preds.begin(); i != preds.end(); i++)
		if (*i != n->id)
			n->preds.insert(*i);
	for (i = succs.begin(); i != succs.end(); i++)
		if (*i != n->id)
			n->succs.insert(*i);
	for (i = interferes.begin(); i != interferes.end(); i++)
		if (*i != n->id)
			n->interferes.insert(*i);


	nblocks_created += 1;

	return n;
}

void NBlockGraph::cpp_is_a_bad_language(const Projection *p, State *initial)
{
	unsigned int init_nblock = p->project(initial);

	nblocks_created = 0;
	project = p;
	num_sigma_zero = num_nblocks = p->get_num_nblocks();
	assert(init_nblock < num_nblocks);

	_blocks = new NBlock*[num_nblocks];
	for(unsigned int i = 0; i < num_nblocks; i += 1)
		_blocks[i] = NULL;

	NBlock *n = create_nblock(init_nblock);
	n->open.add(initial);
	_blocks[init_nblock] = n;
	free_list.add(n);

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
	for (unsigned int i = 0; i < num_nblocks; i += 1)
		if (_blocks[i])
			delete _blocks[i];

	delete[] _blocks;
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
			fp_type cur_f = finished->open.get_best_f();
			fp_type new_f;
			if (free_list.empty())
				new_f = fp_infinity;
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
	fp_type best_f = fp_infinity;
	set<unsigned int>::iterator i;

//	pthread_mutex_lock(&mutex);

	for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
		NBlock *b = get_nblock_if_created(*i);
		if (!b)
			continue;
		if (b->open.empty())
			continue;
		if (!best_b || b->open.get_best_f() < best_f) {
			best_f = b->open.get_best_f();
			best_b = b;
		}
	}

//	pthread_mutex_unlock(&mutex);

	// best_b => best_f != fp_infinity
	assert(best_f != fp_infinity || !best_b);

	return best_b;
}

/**
 * Get the NBlock given by the hash value.
 * This shouldn't be called unless the calling thread has this block
 * assigned to it.
 */
NBlock *NBlockGraph::get_nblock(unsigned int hash)
{
	if (!_blocks[hash])
		_blocks[hash] = create_nblock(hash);

	return _blocks[hash];
}

/**
 * Get the NBlock given by the hash value.  If this nblock has not yet
 * been created then NULL is returned.
 */
NBlock *NBlockGraph::get_nblock_if_created(unsigned int hash)
{
	if (!_blocks[hash])
		return NULL;
	return _blocks[hash];
}

/**
 * Get the statistics on the maximum number of NBlocks assigned at one time.
 */
unsigned int NBlockGraph::get_max_assigned_nblocks(void) const
{

	return nblocks_assigned_max;
}

fp_type NBlockGraph::best_f(void){
	if (free_list.empty())
		return 0.0;
	else
		return free_list.best_f();
}


/**
 * Print an NBlock, but don't take the lock.
 */
void NBlockGraph::__print(ostream &o)
{

	o << "Number of NBlocks: " << num_nblocks << endl;
	o << "Number of NBlocks with sigma zero: " << num_sigma_zero << endl;
	o << "--------------------" << endl;
	o << "Free Blocks:" << endl;
	free_list.print(o);
	o << "--------------------" << endl;
	o << "All Blocks:" << endl;
	for (unsigned int i = 0; i < num_nblocks; i += 1)
		if (_blocks[i])
			_blocks[i]->print(o);
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
	set<unsigned int>::iterator iter;
	NBlock *n = get_nblock(y);

	assert(n->sigma == 0);

	/*
	  \A y' \in predecessors(y) /\ y' /= y,
	  \sigma(y') <- \sigma(y') +- 1

	  \A y' \in successors(y),
	  \A y'' \in predecessors(y'), /\ y'' /= y,
	  \sigma(y'') <- \sigma(y'') +- 1
	*/

	for (iter = n->interferes.begin();
	     iter != n->interferes.end();
	     iter++) {
		NBlock *m = get_nblock(*iter);
		if (m->sigma == 0) {
			assert(delta > 0);
			if (is_free(m))
				free_list.remove(m);
			num_sigma_zero -= 1;
		}
		m->sigma += delta;
		if (m->sigma == 0) {
			if (m->hot)
				set_cold(m);
			if (is_free(m)) {
				free_list.add(m);
				pthread_cond_broadcast(&cond);
			}
			num_sigma_zero += 1;
		}
	}
}

/**
 * Get the f-value of the next best NBlock.
 */
fp_type NBlockGraph::next_nblock_f_value(void)
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
	set<unsigned int>::iterator i;
	fp_type f = b->open.get_best_f();

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
			assert(b->id != *i);
			NBlock *m = get_nblock(*i);
			if (m->hot && m->open.get_best_f() < f)
				goto out;
		}

		b->hot = true;
		for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
			assert(b->id != *i);
			NBlock *m = get_nblock(*i);
			if (is_free(m))
				free_list.remove(m);
			if (m->hot)
				set_cold(m);
			m->sigma_hot += 1;
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
	set<unsigned int>::iterator i;

	b->hot = false;
	for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
		assert(b->id != *i);
		NBlock *m = get_nblock(*i);
		m->sigma_hot -= 1;
		if (is_free(m)) {
			free_list.add(m);
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
	set<unsigned int>::iterator iter;

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
		NBlock *m = get_nblock_if_created(*iter);
		if (!m)
			continue;
		if (m->hot)
			set_cold(m);
	}

	pthread_mutex_unlock(&mutex);
}

/**
 * Get the number of nblocks which were actually created.
 */
unsigned int NBlockGraph::get_ncreated_nblocks(void)
{
	return nblocks_created;
}
