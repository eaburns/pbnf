/**
 * \file wpbnf_search.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-04-18
 */

#if !defined(_OPBNF_SEARCH_H_)
#define _OPBNF_SEARCH_H_

#include <vector>

#include "opbnf/nblock_graph.h"
#include "opbnf/nblock.h"
#include "util/thread.h"
#include "util/atomic_int.h"
#include "util/cumulative_ave.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

namespace OPBNF {

class OPBNFSearch : public Search {
public:
	OPBNFSearch(unsigned int n_threads, unsigned int min_expansions);

	virtual ~OPBNFSearch(void);

	virtual vector<State *> *search(Timer *t, State *initial);
private:
	void set_path(vector<State *> *path);

	class PBNFThread : public Thread {
	public:
		PBNFThread(NBlockGraph *graph, OPBNFSearch *search);
		~PBNFThread(void);
		void run(void);
		fp_type get_ave_exp_per_nblock(void);
		fp_type get_ave_open_size(void);
	private:
		vector<State *> *search_nblock(NBlock *n);
		bool should_switch(NBlock *n);

		unsigned int expansions; /* for testing switch */
		NBlockGraph *graph;
		OPBNFSearch *search;
		bool set_hot;
		unsigned long exp_this_block;
		CumulativeAverage ave_exp_per_nblock;
		CumulativeAverage ave_open_size;
		fp_type next_best;
	};

	unsigned int n_threads;
	const Projection *project;
	pthread_mutex_t path_mutex;
	vector<State *> *path;
	AtomicInt bound;
	bool done;

	bool dynamic_m;

	NBlockGraph *graph;
	static AtomicInt min_expansions;
	Timer graph_timer;

	fp_type weight;
	fp_type b;
};
}

#endif	/* !_PBNF_SEARCH_H_ */
