/**
 * \file wbfpsdd_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-20
 */

#if !defined(_WBFPSDD_H_)
#define _WBFPSDD_H_

#include <pthread.h>

#include <vector>

#include "wbfpsdd/nblock.h"
#include "wbfpsdd/nblock_graph.h"
#include "util/thread.h"
#include "util/cumulative_ave.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

class WBFPSDDSearch : public Search {
public:
	WBFPSDDSearch(unsigned int n_threads, fp_type multiplier, unsigned int min_expansions);
	WBFPSDDSearch(unsigned int n_threads, fp_type multiplier, unsigned int min_expansions, fp_type bound);
	virtual ~WBFPSDDSearch(void);

	virtual vector<State *> *search(State *s);

	void set_bound(fp_type bound);
private:

	void set_path(vector<State *> *path);
	bool path_found(void) const;

	class WBFPSDDThread : public Thread {
	public:
		WBFPSDDThread(WBFPSDD::NBlockGraph *graph,
			      WBFPSDDSearch *search);
		~WBFPSDDThread();
		void run(void);
		fp_type get_ave_exp_per_nblock(void);
	private:
		vector<State *> *search_nblock(WBFPSDD::NBlock *n);
		WBFPSDD::NBlockGraph *graph;
		WBFPSDDSearch *search;
		unsigned long exp_this_block;
		CumulativeAverage ave_exp_per_nblock;
	};

	AtomicInt bound;
	unsigned int n_threads;
	const Projection *project;
	vector<State *> *path;
	WBFPSDD::NBlockGraph *graph;
	pthread_mutex_t path_mutex;
	unsigned int min_expansions;
	fp_type multiplier;

	bool done;
	fp_type weight;
};

#endif	/* !_WBFPSDD_H_ */
