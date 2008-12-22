/* -*- mode:linux -*- */
/**
 * \file pbnf_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#include <assert.h>
#include <math.h>

#include <vector>

#include "pbnf_search.h"
#include "search.h"
#include "state.h"

using namespace std;
using namespace PBNF;

PBNFSearch::PBNFThread::PBNFThread(NBlockGraph *graph, PBNFSearch *search)
	: graph(graph), search(search) {}


PBNFSearch::PBNFThread::~PBNFThread(void) {}


/**
 * Run the search thread.
 */
void PBNFSearch::PBNFThread::run(void)
{
	vector<const State *> *path;
	NBlock *n = NULL;

	do {
		n = graph->next_nblock(n);
		if (n) {
			expansions = 0;
			path = search_nblock(n);

			if (path)
				search->set_path(path);
		}
	} while (n);

	graph->set_done();
}


/**
 * Search a single NBlock.
 */
vector<const State *> *PBNFSearch::PBNFThread::search_nblock(NBlock *n)
{
	vector<const State *> *path = NULL;
	OpenList *open = &n->open;
	ClosedList *closed = &n->closed;

	while (!open->empty() && !should_switch(n)) {
		const State *s = open->take();

		if (s->get_f() >= search->bound.read()) {
			delete s;
			open->delete_all_states();
			break;
		}

		const State *dup = closed->lookup(s);
		if (dup && dup->get_f() <= s->get_f()) {
			delete s;
			continue;
		}

		closed->add(s);
		if (dup)
			delete dup;

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;

		vector<const State *> *children = search->expand(s);
		vector<const State *>::iterator iter;

 		for (iter = children->begin(); iter != children->end(); iter++) {
			if ((*iter)->get_f() >= search->bound.read()) {
				delete *iter;
				continue;
			}
			unsigned int block = search->project->project(*iter);
			OpenList *next_open = &graph->get_nblock(block)->open;

			next_open->add(*iter);

		}
		delete children;
	}

	return path;
}


/**
 * Test the graph to see if we should switch to a new NBlock.
 * \param n The current NBlock.
 *
 * \note We should make this more complex... we should also check our
 *       successor NBlocks.
 */
bool PBNFSearch::PBNFThread::should_switch(NBlock *n)
{
	bool ret;

	if (expansions < search->min_expansions)
		return false;

	expansions = 0;

	double free = graph->next_nblock_f_value();
	double cur = n->open.peek()->get_f();

	if (search->detect_livelocks) {
		NBlock *best_scope = graph->best_in_scope(n);
		double scope = best_scope->open.get_best_f();

		ret = free < cur || scope < cur;
		if (!ret)
			graph->wont_release(n);
		else if (scope < free)
			graph->set_hot(best_scope);
	} else {
		ret = free + search->delta_f < cur;
	}

	return ret;
}


/************************************************************/


PBNFSearch::PBNFSearch(unsigned int n_threads,
		       unsigned int min_expansions,
		       float delta_f,
		       bool detect_livelocks)
	: n_threads(n_threads),
	  project(NULL),
	  path(NULL),
	  bound(INFINITY),
	  detect_livelocks(detect_livelocks),
	  min_expansions(min_expansions),
	  delta_f(0.0)
{
	pthread_mutex_init(&path_mutex, NULL);
}


PBNFSearch::~PBNFSearch(void) {}


vector<const State *> *PBNFSearch::search(const State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<Thread *> threads;
	vector<Thread *>::iterator iter;

	NBlockGraph *graph = new NBlockGraph(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		Thread *t = new PBNFThread(graph, this);
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
 * Set an incumbant solution.
 */
void PBNFSearch::set_path(vector<const State *> *path)
{
	pthread_mutex_lock(&path_mutex);
	assert(path->at(0)->get_g() == path->at(0)->get_f());
	if (path && bound.read() > path->at(0)->get_g()) {
		this->path = path;
		bound.set(path->at(0)->get_g());
	}
	pthread_mutex_unlock(&path_mutex);
}
