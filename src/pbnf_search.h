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

	static void inc_m();
	static void dec_m();

private:
	void set_path(vector<State *> *path);

	class PBNFThread : public Thread {
	public:
		PBNFThread(NBlockGraph *graph, PBNFSearch *search);
		~PBNFThread(void);
		void run(void);
		fp_type get_ave_exp_per_nblock(void);
	private:
		vector<State *> *search_nblock(NBlock *n);
		bool should_switch(NBlock *n);

		unsigned int expansions; /* for testing switch */
		NBlockGraph *graph;
		PBNFSearch *search;
		bool set_hot;
		unsigned long exp_this_block;
		CumulativeAverage ave_exp_per_nblock;
	};

	unsigned int n_threads;
	const Projection *project;
	pthread_mutex_t path_mutex;
	vector<State *> *path;
	AtomicInt bound;
	bool detect_livelocks;
	bool dynamic_m;

	NBlockGraph *graph;
	static AtomicInt min_expansions;
};

#endif	/* !_PBNF_SEARCH_H_ */