/* -*- mode:linux -*- */
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
#include "projection.h"
#include "search.h"
#include "state.h"

namespace PBNF {}

using namespace std;
using namespace PBNF;

class PBNFSearch : public Search {
public:
	PBNFSearch(unsigned int n_threads);

	virtual ~PBNFSearch(void);

	virtual vector<const State *> *search(const State *initial);

private:
	void set_path(vector<const State *> *path);

	class PBNFThread : public Thread {
	public:
		PBNFThread(NBlockGraph *graph, PBNFSearch *search);
		virtual ~PBNFThread(void);
		virtual void run(void);
	private:
		vector<const State *> *search_nblock(NBlock *n);
		bool should_switch(NBlock *n);

		unsigned int expansions; /* expansions in 1 NBlock */
		NBlockGraph *graph;
		PBNFSearch *search;
	};

	unsigned int n_threads;
	const Projection *project;
	pthread_mutex_t path_mutex;
	vector<const State *> *path;
	float bound;
};

#endif	/* !_PBNF_SEARCH_H_ */
