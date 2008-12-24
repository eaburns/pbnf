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
#include "util/thread.h"
#include "projection.h"
#include "open_list.h"
#include "closed_list.h"

using namespace std;
using namespace PSDD;

/**
 * Create a new PSDD Search thread.
 */
PSDDSearch::PSDDThread::PSDDThread(NBlockGraph *graph, PSDDSearch *search)
	: graph(graph), search(search), lowest_out_of_bounds(INFINITY) {}


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

		exp_this_block = 0;

		path = search_nblock(n);

		if (path) {
			search->set_path(path);
			graph->set_path_found();
		}

		ave_exp_per_nblock.add_val(exp_this_block);

	} while(!search->path_found());
}

float PSDDSearch::PSDDThread::get_ave_exp_per_nblock(void)
{
	return ave_exp_per_nblock.read();
}

/**
 * Search a single NBlock.
 * \param n The NBlock.
 * \return NULL, or a path to a goal.
 */
vector<const State *> *PSDDSearch::PSDDThread::search_nblock(NBlock *n)
{
	vector<const State *> *path = NULL;
	OpenList *cur_open = &n->open[graph->get_cur_layer()];
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

		exp_this_block += 1;

		vector<const State *> *children = search->expand(s);
		vector<const State *>::iterator iter;
		for (iter = children->begin();
		     iter != children->end();
		     iter++) {

			if ((*iter)->get_f() > search->bound.read()) {
				if ((*iter)->get_f() < lowest_out_of_bounds)
					lowest_out_of_bounds = (*iter)->get_f();

				delete *iter;
				continue;
			}

			unsigned int block = search->project->project(*iter);
			NBlock *b = graph->get_nblock(block);
			OpenList *next_open = &b->open[graph->get_next_layer()];
			ClosedList *next_closed = &graph->get_nblock(block)->closed;
			const State *dup = next_closed->lookup(*iter);
			if (dup && dup->get_g() <= (*iter)->get_g()) {
				delete *iter;
				continue;
			}

			next_open->add(*iter);
		}
		delete children;

	}

	return path;
}

float PSDDSearch::PSDDThread::get_lowest_out_of_bounds(void)
{
	return lowest_out_of_bounds;
}


/**********************************************************************/


/**
 * Create a new Parallel Structured Duplicate Detection search.
 */
PSDDSearch::PSDDSearch(unsigned int n_threads)
	: bound(INFINITY),
	  n_threads(n_threads),
	  project(NULL),
	  path(NULL),
	  graph(NULL),
	  lowest_out_of_bounds(INFINITY)
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
	  path(NULL),
	  lowest_out_of_bounds(INFINITY)
{
	pthread_mutex_init(&path_mutex, NULL);
}


/**
 * Destructor.
 */
PSDDSearch::~PSDDSearch(void)
{
	if (graph)
		delete graph;
}


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

	vector<PSDDThread *> threads;
	vector<PSDDThread *>::iterator iter;
	float sum = 0.0;
	unsigned int num = 0;
	graph = new NBlockGraph(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		PSDDThread *t = new PSDDThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		if ((*iter)->get_lowest_out_of_bounds()
		    < lowest_out_of_bounds) {
			lowest_out_of_bounds =
				(*iter)->get_lowest_out_of_bounds();
		}

		float ave = (*iter)->get_ave_exp_per_nblock();
		if (ave != 0.0) {
			sum += ave;
			num += 1;
		}

		delete *iter;
	}
	cout << "expansions-per-nblock: " << sum / num << endl;

	return path;
}

/**
 * Set the bound.
 */
void PSDDSearch::set_bound(float bound)
{
	this->bound.set(bound);
}

float PSDDSearch::get_lowest_out_of_bounds(void)
{
	return lowest_out_of_bounds;
}
