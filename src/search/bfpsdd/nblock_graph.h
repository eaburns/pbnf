/**
 * \file nblock_graph.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_BFPSDD_NBLOCK_GRAPH_H_)
#define _BFPSDD_NBLOCK_GRAPH_H_

#include <assert.h>
#include <pthread.h>

#include <iostream>
#include <map>
#include <list>
#include <vector>

#include "../state.h"
#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "../projection.h"
#include "nblock.h"

using namespace std;

namespace BFPSDD {

	template<class NBlockPQ, class StateCompare>
		class NBlockGraph {
	public:
		enum layer { LAYERA = 0, LAYERB };

		NBlockGraph(const Projection *p, State *init);

		~NBlockGraph();

		NBlock<StateCompare> *next_nblock(NBlock<StateCompare> *finished);
		NBlock<StateCompare> *get_nblock(unsigned int hash);
		void set_path_found(void);

		void print(ostream &o);
		unsigned int get_max_assigned_nblocks(void) const;

		float get_layer_value(void) const;

	private:
		void __print(ostream &o);
		void update_scope_sigmas(unsigned int y, int delta);
		void update_sigma(NBlock<StateCompare> *yblk, int delta);

		/* NBlocks. */
		map<unsigned int, NBlock<StateCompare> *> blocks;

		/* The total number of NBlocks. */
		unsigned int num_nblocks;

		/* The number of NBlocks with sigma values of zero. */
		unsigned int num_sigma_zero;

		/* list of free nblock numbers */
		list<NBlock<StateCompare> *> free_list;

		/* prio-queue of NBlocks. */
		NBlockPQ nblock_pq;

		/* The value of this layer */
		float layer_value;


		pthread_mutex_t mutex;
		pthread_cond_t cond;

		/* This flag is set when a thread finds a path so that other
		 * threads do not continue to wait for a new NBlock. */
		bool path_found;


		/*
		 * Statistics
		 */
		unsigned int nblocks_assigned;
		unsigned int nblocks_assigned_max;
	};




/**
 * Create a new NBlock graph.
 * \param p The projection function.
 */
	template<class NBlockPQ, class StateCompare>
		NBlockGraph<NBlockPQ, StateCompare>::NBlockGraph(const Projection *p,
								 State *initial)
	{
		typename map<unsigned int, NBlock<StateCompare> *>::iterator iter;
		unsigned int init_nblock = p->project(initial);

		num_sigma_zero = num_nblocks = p->get_num_nblocks();
		assert(init_nblock < num_nblocks);

		for (unsigned int i = 0; i < num_nblocks; i += 1) {
			NBlock<StateCompare> *n = new NBlock<StateCompare>(i);
			if (i == init_nblock) {
				n->open.add(initial);
				n->closed.add(initial);
				free_list.push_back(n);
				layer_value = n->open.get_best_val();
			}

			blocks[i] = n;
		}

		// Now connect the graph.
		for (iter = blocks.begin(); iter != blocks.end(); iter++) {
			NBlock<StateCompare> *n = iter->second;
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



		pthread_mutex_init(&mutex, NULL);
		pthread_cond_init(&cond, NULL);
		path_found = false;

		nblocks_assigned = 0;
		nblocks_assigned_max = 0;
	}

/**
 * Destroy an NBlock graph.
 */
	template<class NBlockPQ, class StateCompare>
		NBlockGraph<NBlockPQ, StateCompare>::~NBlockGraph()
	{
		typename map<unsigned int, NBlock<StateCompare> *>::iterator iter;

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
	template<class NBlockPQ, class StateCompare>
		NBlock<StateCompare> *
		NBlockGraph<NBlockPQ, StateCompare>::next_nblock(NBlock<StateCompare> *finished)
	{
		NBlock<StateCompare> *n = NULL;

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
			if (!finished->open.empty())
				nblock_pq.add(finished);

			update_scope_sigmas(finished->id, -1);
			finished->inuse = false;

			if (free_list.size() == 0
			    && num_sigma_zero == num_nblocks) {
				// If there are no NBlocks that are currently
				// free with nodes on them, and all of the
				// NBlocks have sigma values of zero:
				// Switch to the next iteration
				typename map<unsigned int, NBlock<StateCompare> *>::iterator iter;

/*
				if (nblock_pq.top()->open.empty())
					goto out;
*/

				// Switch layers -- fill the freelist with the
				// nblocks that have the next layer's value
				layer_value = nblock_pq.top()->open.get_best_val();
				while (!nblock_pq.empty()
				       && nblock_pq.top()->open.get_best_val() == layer_value) {
					free_list.push_back(nblock_pq.take());
				}

				if (free_list.empty())
					path_found = true;

				// Wake up everyone...
				pthread_cond_broadcast(&cond);
			}
		}

		while (free_list.empty() && !path_found)
			pthread_cond_wait(&cond, &mutex);

		if (path_found)
			goto out;

		n = free_list.front();
		n->inuse = true;
		assert(n->open.get_best_val() == layer_value);
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
	template<class NBlockPQ, class StateCompare>
		NBlock<StateCompare> *NBlockGraph<NBlockPQ, StateCompare>::get_nblock(unsigned int hash)
	{
		return blocks[hash];
	}


/**
 * Signal anyone else that is waiting that a path has been found and
 * there is no need to get a new NBlock.
 */
	template<class NBlockPQ, class StateCompare>
		void NBlockGraph<NBlockPQ, StateCompare>::set_path_found(void)
	{
		pthread_mutex_lock(&mutex);
		path_found = true;
		pthread_cond_broadcast(&cond);
		pthread_mutex_unlock(&mutex);
	}


/**
 * Get the statistics on the maximum number of NBlocks assigned at one time.
 */
	template<class NBlockPQ, class StateCompare>
		unsigned int
		NBlockGraph<NBlockPQ, StateCompare>::get_max_assigned_nblocks(void) const
	{

		return nblocks_assigned_max;
	}


/**
 * Print an NBlock, but don't take the lock.
 */
	template<class NBlockPQ, class StateCompare>
		void NBlockGraph<NBlockPQ, StateCompare>::__print(ostream &o)
	{
		typename map<unsigned int, NBlock<StateCompare> *>::iterator biter;
		typename list<NBlock<StateCompare> *>::iterator fiter;

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
	template<class NBlockPQ, class StateCompare>
		void NBlockGraph<NBlockPQ, StateCompare>::print(ostream &o)
	{
		pthread_mutex_lock(&mutex);
		__print(o);
		pthread_mutex_unlock(&mutex);
	}

/**
 * Update the sigma value of a block, add it to the freelist if need
 * be, or remove it from the freelist.
 */
	template<class NBlockPQ, class StateCompare>
		void
		NBlockGraph<NBlockPQ, StateCompare>::update_sigma(NBlock<StateCompare> *yblk,
								  int delta)
	{
		if (yblk->sigma == 0) {
			assert(delta > 0);
			if (!yblk->open.empty())
				free_list.remove(yblk);
			assert(!yblk->inuse);
			nblock_pq.remove(yblk);
			num_sigma_zero -= 1;
		}

		yblk->sigma += delta;

		if (yblk->sigma == 0) {
			if (!yblk->open.empty()) {
				assert(!yblk->inuse);
				if (yblk->open.get_best_val() == layer_value) {
					free_list.push_back(yblk);
					pthread_cond_signal(&cond);
				} else {
					nblock_pq.add(yblk);
				}
			}
			num_sigma_zero += 1;
		}
	}

/**
 * Update the sigmas by delta for all of the predecessors of y and all
 * of the predecessors of the successors of y.
 */
	template<class NBlockPQ, class StateCompare>
		void
		NBlockGraph<NBlockPQ, StateCompare>::update_scope_sigmas(unsigned int y,
									 int delta)
	{
		typename set<NBlock<StateCompare> *>::iterator iter;

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

	template<class NBlockPQ, class StateCompare>
		float NBlockGraph<NBlockPQ, StateCompare>::get_layer_value(void) const
	{
		return layer_value;
	}

} /* BFPSDD */

#endif	/* !_BFPSDD_NBLOCK_GRAPH_H_ */
