/**
 * \file bfpsdd_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-20
 */

#if !defined(_BFPSDD_H_)
#define _BFPSDD_H_

#include <pthread.h>

#include <vector>

#include "bfpsdd/nblock.h"
#include "bfpsdd/nblock_graph.h"
#include "bfpsdd/real_val_nblock_pq.h"
#include "util/thread.h"
#include "util/cumulative_ave.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

class BFPSDDSearch : public Search {
public:
	BFPSDDSearch(unsigned int n_threads);
	BFPSDDSearch(unsigned int n_threads, float bound);
	virtual ~BFPSDDSearch(void);

	virtual vector<State *> *search(State *s);

	void set_bound(float bound);
private:

	void set_path(vector<State *> *path);
	bool path_found(void) const;

	class BFPSDDThread : public Thread {
	public:
		BFPSDDThread(BFPSDD::NBlockGraph<BFPSDD::RealValNBlockPQ<CompareOnF>, CompareOnF> *graph,
			   BFPSDDSearch *search);
		~BFPSDDThread();
		void run(void);
		float get_ave_exp_per_nblock(void);
	private:
		vector<State *> *search_nblock(BFPSDD::NBlock<CompareOnF> *n);
		BFPSDD::NBlockGraph<BFPSDD::RealValNBlockPQ<CompareOnF>, CompareOnF> *graph;
		BFPSDDSearch *search;
		unsigned long exp_this_block;
		CumulativeAverage ave_exp_per_nblock;
	};

	AtomicFloat bound;
	unsigned int n_threads;
	const Projection *project;
	vector<State *> *path;
	BFPSDD::NBlockGraph<BFPSDD::RealValNBlockPQ<CompareOnF>, CompareOnF> *graph;
	pthread_mutex_t path_mutex;
};

#endif	/* !_BFPSDD_H_ */
