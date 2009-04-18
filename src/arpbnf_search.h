/**
 * \file arpbnf_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#if !defined(_ARPBNF_SEARCH_H_)
#define _ARPBNF_SEARCH_H_

#include <vector>

using namespace std;

#include "arpbnf/nblock_graph.h"
#include "arpbnf/nblock.h"
#include "util/thread.h"
#include "util/atomic_int.h"
#include "util/cumulative_ave.h"
#include "util/sync_solution_stream.h"
#include "projection.h"
#include "search.h"
#include "state.h"

namespace ARPBNF {

	using namespace std;
	using namespace ARPBNF;

	class ARPBNFSearch : public Search {
	public:
		ARPBNFSearch(unsigned int n_threads,
			     unsigned int min_expansions,
			     vector<double> *w);

		virtual ~ARPBNFSearch(void);

		virtual vector<State *> *search(Timer *t, State *initial);
		virtual void output_stats(void);

	private:
		void set_path(vector<State *> *path);

		/*
		 * Datamembers
		 */
		unsigned int n_threads;
		const Projection *project;

		SolutionStream *solutions;
		AtomicInt bound;

		NBlockGraph *graph;
		unsigned int min_expansions;

		vector<double> *weights;
		unsigned int next_weight;

		/********************************************/

		/**
		 * A single ARPBNFSearch thread
		 */
		class ARPBNFThread : public Thread {
		public:
			ARPBNFThread(NBlockGraph *graph, ARPBNFSearch *search);
			~ARPBNFThread(void);
			void run(void);
		private:
			vector<State *> *process_child(State *ch);
			vector<State *> *search_nblock(NBlock *n);
			bool should_switch(NBlock *n);

			unsigned int expansions; /* for testing switch */
			NBlockGraph *graph;
			ARPBNFSearch *search;
			bool set_hot;
		};
	};
}

#endif	/* !_ARPBNF_SEARCH_H_ */
