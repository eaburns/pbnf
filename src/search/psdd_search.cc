/* -*- mode:linux -*- */
/**
 * \file psdd.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-24
 */

#include <pthread.h>
#include <math.h>

#include <iostream>
#include <vector>

#include "psdd_search.h"
#include "psdd/nblock_graph.h"
#include "psdd/nblock.h"
#include "psdd/projection.h"
#include "util/thread.h"
#include "open_list.h"
#include "closed_list.h"

using namespace std;
using namespace PSDD;

/**
 * Create a new PSDD Search thread.
 */
PSDDSearch::PSDDThread::PSDDThread(NBlockGraph *graph, PSDDSearch *search)
	: graph(graph), search(search) {}


PSDDSearch::PSDDThread::~PSDDThread() {}


/**
 * The thread work method for a PSDD search.
 */
void PSDDSearch::PSDDThread::run(void)
{
	vector<const State *> *path;
	NBlock *n = NULL;

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
vector<const State *> *PSDDSearch::PSDDThread::search_nblock(NBlock *n)
{
	vector<const State *> *path = NULL;
	OpenList *cur_open = n->cur_open;
	ClosedList *closed = &n->closed;

	while (!cur_open->empty()) {
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
		for (iter = children->begin(); iter != children->end(); iter++) {
			unsigned int block = search->project->project(*iter);
			OpenList *next_open = graph->get_nblock(block)->next_open;

			if ((*iter)->get_f() < search->bound)
				next_open->add(*iter);
			else
				delete *iter;
		}
		delete children;

	}

	return path;
}


/**
 * Create a new Parallel Structured Duplicate Detection search.
 */
PSDDSearch::PSDDSearch(unsigned int n_threads)
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
PSDDSearch::PSDDSearch(unsigned int n_threads, float bound)
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
PSDDSearch::~PSDDSearch(void) {}


/**
 * Set the path to the goal.
 */
void PSDDSearch::set_path(vector<const State *> *p)
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
bool PSDDSearch::path_found(void) const
{
	return path != NULL;
}

/**
 * Perform the search.
 */
vector<const State *> *PSDDSearch::search(const State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<Thread *> threads;
	vector<Thread *>::iterator iter;

	NBlockGraph *graph = new NBlockGraph(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		Thread *t = new PSDDThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

	cout << "Max NBlocks assigned at once: "
	     << graph->get_max_assigned_nblocks() << endl;
	delete graph;

	return path;
}

/**
 * Set the bound.
 */
void PSDDSearch::set_bound(float bound)
{
	this->bound = bound;
}
