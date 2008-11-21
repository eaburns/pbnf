/* -*- mode:linux -*- */
/**
 * \file psdd.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-24
 */

#if !defined(_PSDD_H_)
#define _PSDD_H_

#include <pthread.h>

#include <vector>

#include "psdd/nblock.h"
#include "psdd/nblock_graph.h"
#include "util/thread.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;
using namespace PSDD;

class PSDDSearch : public Search {
public:
	PSDDSearch(unsigned int n_threads);
	PSDDSearch(unsigned int n_threads, float bound);
	virtual ~PSDDSearch(void);

	virtual vector<const State *> *search(const State *s);

	void set_bound(float bound);
private:

	void set_path(vector<const State *> *path);
	bool path_found(void) const;

	class PSDDThread : public Thread {
	public:
		PSDDThread(NBlockGraph *graph, PSDDSearch *search);
		virtual ~PSDDThread();
		virtual void run(void);
	private:
		vector<const State *> *search_nblock(NBlock *n);
		NBlockGraph *graph;
		PSDDSearch *search;
	};

	AtomicFloat bound;
	unsigned int n_threads;
	const Projection *project;
	vector<const State *> *path;
	pthread_mutex_t path_mutex;
};

#endif	/* !_PSDD_H_ */
