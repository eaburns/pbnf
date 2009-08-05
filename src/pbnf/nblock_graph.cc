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

/**
 * Create the nblock with the given ID.
 */
NBlock *NBlockGraph::create_nblock(unsigned int id)
{
	NBlock *n = new NBlock(project, id);

	nblocks_created += 1;

	return n;
}

/**
 * Apparently gdb can't single step inside a c++ constructor... so we
 * just call this function in the constructor so that we can see what
 * is going on.
 */
void NBlockGraph::cpp_is_a_bad_language(const Projection *p,
					State *initial,
					AtomicInt *b /* bound */,
					double w /* weight */)
{
	unsigned int init_nblock = p->project(initial);

	nblocks_created = 0;
	project = p;
	num_sigma_zero = num_nblocks = p->get_num_nblocks();
	assert(init_nblock < num_nblocks);

	map.set_observer(this);

	NBlock *n = map.get(init_nblock);
	n->open.add(initial);
	n->closed.add(initial);
	free_list.add(n);

	bound = b;
	weight = w;

	done = false;

	switch_locks_forced = 0;
	switch_locks_forced_empty = 0;
	switch_locks_forced_finished = 0;
	total_switches = 0;
	nblocks_assigned = 0;
	nblocks_assigned_max = 0;
}

/**
 * Create a new NBlock graph.
 * \param p The projection function.
 */
NBlockGraph::NBlockGraph(const Projection *p,
			 State *initial,
			 AtomicInt *b /* bound */,
			 double w /* weight */)
	: map(p)
{
	cpp_is_a_bad_language(p, initial, b, w);
}

/**
 * Destroy an NBlock graph.
 */
NBlockGraph::~NBlockGraph()
{
}


/**
 * Get the next nblock for expansion, possibly release a finished
 * nblock.  The next nblock is the one with the minimum f-value.
 *
 * \note This call will block if there are currently no free nblocks.
 * \param finished If non-NULL, the finished nblock will be released
 *        into the next level's free_list.
 * \return The next NBlock to expand or NULL if there is nothing left
 *         to do.
 */
NBlock *NBlockGraph::next_nblock(NBlock *finished)
{
	NBlock *n = NULL;

	// Take the lock, but if someone else already has it, just
	// keep going.
	if (finished && !finished->open.empty()) {
		if (!mutex.try_lock())
			return finished;
	} else {
		if (!finished)
			switch_locks_forced_finished += 1;
		if (finished && finished->open.empty())
			switch_locks_forced_empty += 1;
		switch_locks_forced += 1;
		mutex.lock();
	}
	total_switches += 1;

	if (finished) {		// Release an NBlock
		if (finished->sigma != 0) {
			cerr << "A proc had an NBlock with sigma != 0" << endl;
			finished->print(cerr);
			cerr << endl << endl << endl;
			__print(cerr);
		}
		assert(finished->sigma == 0);

/*
  This is bogus, because what if there is a better block in our scope?
  We would rather get that block than searching the same old ratty
  nblock.

		if (!finished->open.empty()) {
			fp_type cur_f = finished->best_value();
			fp_type new_f;
			if (free_list.empty())
				new_f = fp_infinity;
			else
				new_f = free_list.front()->best_value();
			if (cur_f <= new_f) {
				n = finished;
				goto out;
			}
		}
*/

		nblocks_assigned -= 1;

		finished->inuse = false;
		if (is_free(finished)) {
			free_list.add(finished);
			mutex.cond_signal();
		}

		update_scope_sigmas(finished->id, -1);

	}

retry:

	if (num_sigma_zero == num_nblocks && free_list.empty()) {
		__set_done();
		goto out;
	}

	while (!done && free_list.empty())
		mutex.cond_wait();

	if (done)
		goto out;

	if (free_list.front()->best_value() >= (bound->read() * weight)) {
		// This may be pretty weak, but it should allow for
		// eariler stopping.

		// If all sigma values are zero (no one else is
		// searching) then we will set done on the retry.
		if (num_sigma_zero == num_nblocks)
			cerr << "# -------------------- quitting early" << endl;
		prune_free_list();
		goto retry;
	}

	n = free_list.take();
	if (!n) {
		cerr << "-------------------- !n" << endl;
		abort();
	}

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
	mutex.unlock();

	return n;
}


/**
 * Get the best NBlock in the interference scope of b which is not free.
 */
NBlock *NBlockGraph::best_in_scope(NBlock *b)
{
	NBlock *best_b = NULL;
	fp_type best_val = fp_infinity;
	set<unsigned int>::iterator i;

	for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
		NBlock *b = map.find(*i);
		if (!b)
			continue;
		if (b->open.empty())
			continue;
		if (!best_b || b->best_value() < best_val) {
			best_val = b->best_value();
			best_b = b;
		}
	}

	return best_b;
}

/*
 * Remove all nblocks from the free_list.  The nodes in these nblocks
 * will remain in their open lists, for pruning later... if they ever
 * are added back to the free_list.  They can be added back to the
 * free_list if a processor searches one of their neighbors and they
 * gain a node worth looking at.
 */
void NBlockGraph::prune_free_list(void)
{
	free_list.reset();
}

/**
 * Get the NBlock given by the hash value.
 */
NBlock *NBlockGraph::get_nblock(unsigned int hash)
{
	return map.get(hash);
}

/**
 * Get the statistics on the maximum number of NBlocks assigned at one time.
 */
unsigned int NBlockGraph::get_max_assigned_nblocks(void) const
{

	return nblocks_assigned_max;
}

/**
 * Get the value of the best nblock.
 */
fp_type NBlockGraph::best_val(void)
{
	NBlock *b = NULL;
	b = free_list.front();
	if (b)
		return b->best_value();
	return fp_infinity;
}


/**
 * Print an NBlock, but don't take the lock.
 */
void NBlockGraph::__print(ostream &o)
{
	o << "Number of NBlocks: " << num_nblocks << endl;
	o << "Number of NBlocks with sigma zero: " << num_sigma_zero << endl;
	o << "All Blocks:" << endl;
	for (unsigned int i = 0; i < num_nblocks; i += 1)
		if (map.find(i))
			map.find(i)->print(o);
}

/**
 * Print an NBlockGraph to the given stream.
 */
void NBlockGraph::print(ostream &o)
{
	mutex.lock();
	__print(o);
	mutex.unlock();
}

/**
 * Update the sigmas by delta for all of the predecessors of y and all
 * of the predecessors of the successors of y.
 */
void NBlockGraph::update_scope_sigmas(unsigned int y, int delta)
{
	set<unsigned int>::iterator iter;
	NBlock *n = map.get(y);

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
		NBlock *m = map.get(*iter);
		if (m->sigma == 0) {
			assert(delta > 0);
			if (is_free(m) && m->pq_index != -1)
				free_list.remove(m->pq_index);
			num_sigma_zero -= 1;
		}
		m->sigma += delta;
		if (m->sigma == 0) {
			if (m->hot)
				set_cold(m);
			if (is_free(m)) {
				free_list.add(m);
				mutex.cond_signal();
			}
			num_sigma_zero += 1;
		}
	}
}

/**
 * Sets the done flag with out taking the lock.
 */
void NBlockGraph::__set_done(void)
{
#if !defined(NDEBUG)
	list<NBlock*>::iterator iter;

	for (iter = nblocks.begin(); iter != nblocks.end(); iter++) {
		if (!(*iter)->open.empty())
			cerr << "NBlock " << (*iter)->id << " is not empty" << endl;
		if ((*iter)->hot)
			cerr << "NBlock " << (*iter)->id << " is hot" << endl;
	}
#endif	// NDEBUG

	done = true;
	mutex.cond_broadcast();
}

/**
 * Sets the done flag.
 */
void NBlockGraph::set_done(void)
{
	if (done)
		return;
	mutex.lock();
	if (done) {
		mutex.unlock();
		return;
	}
	__set_done();
	mutex.lock();
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
 *
 * \return true if the block is successfully set to hot, false
 *         otherwise.
 */
bool NBlockGraph::set_hot(NBlock *b)
{
	set<unsigned int>::iterator i;
	fp_type val = b->best_value();

	if (!mutex.try_lock())
		return false;

	if (!b->hot && b->sigma > 0) {
		for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
			assert(b->id != *i);
			NBlock *m = map.get(*i);
			if (m->hot && m->best_value() < val)
				goto out;
		}

		b->hot = true;
		for (i = b->interferes.begin(); i != b->interferes.end(); i++) {
			assert(b->id != *i);
			NBlock *m = map.get(*i);
			if (is_free(m) && m->pq_index != -1)
				free_list.remove(m->pq_index);
			if (m->hot)
				set_cold(m);
			m->sigma_hot += 1;
		}
	}
out:
	mutex.unlock();
	return true;
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
		NBlock *m = map.get(*i);
		m->sigma_hot -= 1;
		if (is_free(m)) {
			free_list.add(m);
			mutex.cond_signal();
		}
	}
}

/**
 * We won't release block b, so set all hot blocks in its interference
 * scope back to cold.
 */
void NBlockGraph::wont_release(NBlock *b)
{
	set<unsigned int>::iterator iter;

	// Don't bother locking if nothing is hot anyway.
	if (b->sigma_hot == 0)
		return;

	if (!mutex.try_lock())
		return;

	for (iter = b->interferes.begin();
	     iter != b->interferes.end();
	     iter++) {
		NBlock *m = map.find(*iter);
		if (!m)
			continue;
		if (m->hot)
			set_cold(m);
	}

	mutex.unlock();
}

/**
 * Get the number of nblocks which were actually created.
 */
unsigned int NBlockGraph::get_ncreated_nblocks(void)
{
	return map.get_num_created();;
}

void NBlockGraph::print_stats(ostream &o)
{
	Mutex::print_stats(o);

	//
	// Print open list statistics.
	//
	list<NBlock*>::iterator iter;
	unsigned int max = 0;
	double sum = 0;
	double num = 0;
	for (iter = nblocks.begin(); iter != nblocks.end(); iter++) {
		NBlock *n = *iter;
		if (n->open.get_max_size() > max)
			max = n->open.get_max_size();
		sum += n->open.get_avg_size();
		num += 1;
	}
	if (num > 0) {
		cout << "average-open-size: " << (sum / num) << endl;
		cout << "max-open-size: " << max << endl;
	} else {
		cout << "average-open-size: -1" << endl;
		cout << "max-open-size: -1" << endl;
	}

	cout << "# switch-locks-forced: " << switch_locks_forced << endl;
	cout << "# switch-locks-forced_empty: "
	     << switch_locks_forced_empty << endl;
	cout << "# switch-locks-forced_finished: "
	     << switch_locks_forced_finished << endl;
	cout << "# total-switches: " << total_switches << endl;
}

void NBlockGraph::observe(NBlock *b)
{
	nblocks.push_back(b);
}
