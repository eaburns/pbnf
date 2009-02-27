/**
 * \file pbnf_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#if !defined(_PBNF_SEARCH_H_)
#define _PBNF_SEARCH_H_

#include <vector>

#include "pbnf/nblock_graph.h"
#include "pbnf/nblock.h"
#include "util/thread.h"
#include "util/atomic_int.h"
#include "util/cumulative_ave.h"
#include "projection.h"
#include "search.h"
#include "state.h"

namespace PBNF {}

using namespace std;
using namespace PBNF;

class PBNFSearch : public Search {
public:
	PBNFSearch(unsigned int n_threads, unsigned int min_expansions,
		   bool detect_livelocks);

	virtual ~PBNFSearch(void);

	virtual vector<State *> *search(State *initial);
	virtual void output_stats(void);

	static void inc_switch(bool failed);

private:
	void set_path(vector<State *> *path);

	class PBNFThread : public Thread {
	public:
		PBNFThread(NBlockGraph *graph, PBNFSearch *search);
		~PBNFThread(void);
		void run(void);
		fp_type get_ave_exp_per_nblock(void);
		fp_type get_ave_open_size(void);
	private:
		vector<State *> *search_nblock(NBlock *n);
		bool should_switch(NBlock *n);

		unsigned int expansions; /* for testing switch */
		NBlockGraph *graph;
		PBNFSearch *search;
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
	bool detect_livelocks;
	bool dynamic_m;

	NBlockGraph *graph;
	AtomicInt min_expansions;
	static AtomicInt failed;
	static AtomicInt succeeded;

	/* stats tracking */
	fp_type sum;
	unsigned int num;
	fp_type osum;
	unsigned int onum;
};

#endif	/* !_PBNF_SEARCH_H_ */
