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
		NBlockGraph(Projection *p, const State *init);

		~NBlockGraph();

		NBlock *next_nblock(NBlock *finished);
		NBlock *get_nblock(unsigned int hash);
		float next_nblock_f_value(void);
		void set_path_found(void);
		void print(ostream &o);
		unsigned int get_max_assigned_nblocks(void) const;

	private:
		void __print(ostream &o);
		void update_scope_sigmas(unsigned int y, int delta);
		void update_sigma(unsigned int y, int delta);

		/* NBlocks. */
		map<unsigned int, NBlock *> blocks;

		/* The total number of NBlocks. */
		unsigned int num_nblocks;

		/* The number of NBlocks with sigma values of zero. */
		unsigned int num_sigma_zero;

		/* list of free nblock numbers */
		NBlockFreeList free_list;

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
} /* PBNF */

#endif	/* !_NBLOCK_GRAPH_H_ */
