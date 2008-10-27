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

#include "projection.h"
#include "nblock.h"
#include "nblock_graph.h"
#include "../util/thread.h"
#include "../search.h"
#include "../state.h"

using namespace std;

class PSDD : public Search {
public:
	PSDD(unsigned int n_threads);
	PSDD(unsigned int n_threads, float bound);
	virtual ~PSDD(void);

	virtual vector<const State *> *search(const State *s);

	void set_bound(float bound);
private:

	void set_path(vector<const State *> *path);
	bool path_found(void) const;

	class PSDDThread : public Thread {
	public:
		PSDDThread(NBlockGraph *graph, PSDD *search);
		virtual ~PSDDThread();
		virtual void run(void);
	private:
		vector<const State *> *search_nblock(NBlock *n);
		NBlockGraph *graph;
		PSDD *search;
	};

	float bound;
	unsigned int n_threads;
	Projection *project;
	vector<const State *> *path;
	pthread_mutex_t path_mutex;
};

#endif	/* !_PSDD_H_ */
