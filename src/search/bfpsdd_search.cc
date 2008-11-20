/* -*- mode:linux -*- */
/**
 * \file bfpsdd_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-20
 */


#include <pthread.h>
#include <math.h>

#include <iostream>
#include <vector>

#include "bfpsdd_search.h"
#include "bfpsdd/real_val_nblock_pq.h"
#include "bfpsdd/nblock_graph.h"
#include "bfpsdd/nblock.h"
#include "util/thread.h"
#include "projection.h"
#include "open_list.h"
#include "closed_list.h"

using namespace std;
using namespace BFPSDD;

/**
 * Create a new PSDD Search thread.
 */
BFPSDDSearch::BFPSDDThread::BFPSDDThread(NBlockGraph<BFPSDD::RealValNBlockPQ<CompareOnF>,CompareOnF> *graph,
	BFPSDDSearch *search)
	: graph(graph), search(search) {}


BFPSDDSearch::BFPSDDThread::~BFPSDDThread() {}


/**
 * The thread work method for a PSDD search.
 */
void BFPSDDSearch::BFPSDDThread::run(void)
{
	vector<const State *> *path;
	NBlock<CompareOnF> *n = NULL;

	do {
		n = graph->next_nblock(n);
		if (!n)		// no solution
			break;

		path = search_nblock(n);

		if (path) {
			search->set_path(path);
			graph->set_path_found();
		}

	} while(!search->path_found());
}


/**
 * Search a single NBlock.
 * \param n The NBlock.
 * \return NULL, or a path to a goal.
 */
vector<const State *> *BFPSDDSearch::BFPSDDThread::search_nblock(NBlock<CompareOnF> *n)
{
	vector<const State *> *path = NULL;
	PQOpenList<CompareOnF> *cur_open = &n->open;
	ClosedList *closed = &n->closed;

	while (!cur_open->empty()) {
		if (cur_open->get_best_val() > graph->get_layer_value())
			break;

		const State *s = cur_open->take();
		const State *dup = closed->lookup(s);
		if (dup) {
			delete s;
			continue;
		}

		closed->add(s);

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		vector<const State *> *children = search->expand(s);
		vector<const State *>::iterator iter;
		for (iter = children->begin();
		     iter != children->end();
		     iter++) {
			unsigned int block = search->project->project(*iter);
			NBlock<CompareOnF> *b = graph->get_nblock(block);
			OpenList *next_open = &b->open;

			if ((*iter)->get_f() < search->bound)
				next_open->add(*iter);
			else
				delete *iter;
		}
		delete children;

	}

	return path;
}


/**********************************************************************/


/**
 * Create a new Parallel Structured Duplicate Detection search.
 */
BFPSDDSearch::BFPSDDSearch(unsigned int n_threads)
	: bound(INFINITY),
	  n_threads(n_threads),
	  project(NULL),
	  path(NULL)
{
	pthread_mutex_init(&path_mutex, NULL);
}

/**
 * Create a new Parallel Structured Duplicate Detection search with a
 * given bound.
 */
BFPSDDSearch::BFPSDDSearch(unsigned int n_threads, float bound)
	: bound(bound),
	  n_threads(n_threads),
	  project(NULL),
	  path(NULL)
{
	pthread_mutex_init(&path_mutex, NULL);
}


/**
 * Destructor.
 */
BFPSDDSearch::~BFPSDDSearch(void) {}


/**
 * Set the path to the goal.
 */
void BFPSDDSearch::set_path(vector<const State *> *p)
{
	pthread_mutex_lock(&path_mutex);
	if (path) {
		vector<const State *>::iterator iter;

		for (iter = p->begin(); iter != p->end(); iter++)
			delete *iter;

		delete p;
	} else {
		path = p;
	}
	pthread_mutex_unlock(&path_mutex);
}


/**
 * Test if there has been a path to the goal found yet.
 */
bool BFPSDDSearch::path_found(void) const
{
	return path != NULL;
}

/**
 * Perform the search.
 */
vector<const State *> *BFPSDDSearch::search(const State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<Thread *> threads;
	vector<Thread *>::iterator iter;

	NBlockGraph<RealValNBlockPQ<CompareOnF>, CompareOnF> *graph =
		new NBlockGraph<RealValNBlockPQ<CompareOnF>, CompareOnF>(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		Thread *t = new BFPSDDThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

	delete graph;

	return path;
}

/**
 * Set the bound.
 */
void BFPSDDSearch::set_bound(float bound)
{
	this->bound = bound;
}
