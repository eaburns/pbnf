/* -*- mode:linux -*- */
/**
 * \file nblock_graph.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_NBLOCK_GRAPH_H_)
#define _NBLOCK_GRAPH_H_

#include <pthread.h>

#include <iostream>
#include <map>
#include <vector>

#include "nblock_free_list.h"
#include "nblock.h"
#include "../state.h"
#include "../closed_list.h"
#include "../queue_open_list.h"
#include "../open_list.h"
#include "../projection.h"

using namespace std;

namespace PBNF {
	class NBlockGraph {
	public:
		NBlockGraph(const Projection *p, const State *init);

		~NBlockGraph();

		NBlock *next_nblock(NBlock *finished);
		NBlock *get_nblock(unsigned int hash);
		float next_nblock_f_value(void);
		void print(ostream &o);
		unsigned int get_max_assigned_nblocks(void) const;
		void set_done(void);
		NBlock *best_in_scope(NBlock *b);
		void wont_release(NBlock *b);
		void set_hot(NBlock *b);

	private:
		void __set_done(void);
		void __print(ostream &o);
		bool is_free(NBlock *b);
		void set_cold(NBlock *b);
		void update_scope_sigmas(unsigned int y, int delta);

		/* NBlocks. */
		map<unsigned int, NBlock *> blocks;

		/* The total number of NBlocks. */
		unsigned int num_nblocks;

		/* The number of NBlocks with sigma values of zero. */
		unsigned int num_sigma_zero;

		/* list of free nblock numbers */
		NBlockFreeList free_list;

		/* This flag is set when the search is completed to
		 * signal to all waiting processess that the search
		 * has completed. */
		bool done;

		pthread_mutex_t mutex;
		pthread_cond_t cond;

		/*
		 * Statistics
		 */
		unsigned int nblocks_assigned;
		unsigned int nblocks_assigned_max;
	};
} /* PBNF */

#endif	/* !_NBLOCK_GRAPH_H_ */
