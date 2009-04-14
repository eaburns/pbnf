/**
 * \file wpbnf_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#if !defined(_WPBNF_SEARCH_H_)
#define _WPBNF_SEARCH_H_

#include <vector>

#include "wpbnf/nblock_graph.h"
#include "wpbnf/nblock.h"
#include "util/thread.h"
#include "util/atomic_int.h"
#include "util/cumulative_ave.h"
#include "projection.h"
#include "search.h"
#include "state.h"

namespace WPBNF {}

using namespace std;
using namespace WPBNF;

class WPBNFSearch : public Search {
public:
	WPBNFSearch(unsigned int n_threads, unsigned int min_expansions);

	virtual ~WPBNFSearch(void);

	virtual vector<State *> *search(Timer *t, State *initial);

	void output_stats(void);
private:
	void set_path(vector<State *> *path);

	class PBNFThread : public Thread {
	public:
		PBNFThread(NBlockGraph *graph, WPBNFSearch *search);
		~PBNFThread(void);
		void run(void);
		fp_type get_ave_exp_per_nblock(void);
		fp_type get_ave_open_size(void);
	private:
		vector<State *> *search_nblock(NBlock *n);
		bool should_switch(NBlock *n);

		unsigned int expansions; /* for testing switch */
		NBlockGraph *graph;
		WPBNFSearch *search;
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

	fp_type weight;


	/* stats tracking */
	fp_type sum;
	unsigned int num;
	fp_type osum;
	unsigned int onum;
	Timer graph_timer;
};

#endif	/* !_PBNF_SEARCH_H_ */
