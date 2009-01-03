/**
 * \file bfpsdd_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-20
 */


#include <pthread.h>

#include <limits>
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
	vector<State *> *path;
	NBlock<CompareOnF> *n = NULL;

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

float BFPSDDSearch::BFPSDDThread::get_ave_exp_per_nblock(void)
{
	return ave_exp_per_nblock.read();
}

/**
 * Search a single NBlock.
 * \param n The NBlock.
 * \return NULL, or a path to a goal.
 */
vector<State *> *BFPSDDSearch::BFPSDDThread::search_nblock(NBlock<CompareOnF> *n)
{
	vector<State *> *path = NULL;
	PQOpenList<CompareOnF> *cur_open = &n->open;

	while (!cur_open->empty()) {
		if (cur_open->get_best_val() > graph->get_layer_value())
			break;

		State *s = cur_open->take();

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		exp_this_block += 1;

		vector<State *> *children = search->expand(s);
		vector<State *>::iterator iter;
		for (iter = children->begin();
		     iter != children->end();
		     iter++) {
			unsigned int block = search->project->project(*iter);
			NBlock<CompareOnF> *b = graph->get_nblock(block);
			OpenList *next_open = &b->open;
			ClosedList *next_closed = &graph->get_nblock(block)->closed;
			if ((*iter)->get_f() > search->bound.read()) {
				delete *iter;
				continue;
			}
			State *dup = next_closed->lookup(*iter);
			if (dup) {
				if (dup->get_g() > (*iter)->get_g()) {
					dup->update((*iter)->get_parent(),
						    (*iter)->get_g());
					if (!dup->is_open())
						next_open->add(dup);
				}
				delete *iter;
			} else {
				next_closed->add(*iter);
				if ((*iter)->is_goal()) {
					path = (*iter)->get_path();
					delete children;
					return path;
				}
				next_open->add(*iter);
			}
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
	: bound(numeric_limits<float>::infinity()),
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
	  path(NULL),
	  graph(NULL)
{
	pthread_mutex_init(&path_mutex, NULL);
}


/**
 * Destructor.
 */
BFPSDDSearch::~BFPSDDSearch(void)
{
	if (graph)
		delete graph;
}


/**
 * Set the path to the goal.
 */
void BFPSDDSearch::set_path(vector<State *> *p)
{
	pthread_mutex_lock(&path_mutex);
	if (path) {
		vector<State *>::iterator iter;

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
vector<State *> *BFPSDDSearch::search(State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<BFPSDDThread *> threads;
	vector<BFPSDDThread *>::iterator iter;
	float sum = 0.0;
	unsigned int num = 0;

	graph = new NBlockGraph<RealValNBlockPQ<CompareOnF>, CompareOnF>(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		BFPSDDThread *t = new BFPSDDThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();

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
void BFPSDDSearch::set_bound(float bound)
{
	this->bound.set(bound);
}
