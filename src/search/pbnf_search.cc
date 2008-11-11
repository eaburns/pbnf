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
		const State *dup = closed->lookup(s);

		if (s->get_f() >= search->bound
		    || (dup && dup->get_f() <= s->get_f())) {
			delete s;
			continue;
		}

		closed->add(s);

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;

		vector<const State *> *children = search->expand(s);
		vector<const State *>::iterator iter;

 		for (iter = children->begin(); iter != children->end(); iter++) {
			unsigned int block = search->project->project(*iter);
			OpenList *next_open = &graph->get_nblock(block)->open;

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
 * Test the graph to see if we should switch to a new NBlock.
 * \param n The current NBlock.
 *
 * \note We should make this more complex... we should also check our
 *       successor NBlocks.
 */
bool PBNFSearch::PBNFThread::should_switch(NBlock *n)
{
	const unsigned int MIN_EXPANSIONS = 10;
	bool ret;
	double cur, scope, free;

	if (expansions < MIN_EXPANSIONS)
		return false;

	scope = graph->best_in_scope(n);
	free = graph->next_nblock_f_value();
	cur = n->open.peek()->get_f();

	ret = cur < free || cur < scope;

	if (!ret)
		graph->wont_release(n);
	return ret;
}


/************************************************************/


PBNFSearch::PBNFSearch(unsigned int n_threads)
	: n_threads(n_threads),
	  project(NULL),
	  path(NULL),
	  bound(INFINITY)
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
	if (path && bound > path->at(0)->get_g()) {
		this->path = path;
		bound = path->at(0)->get_g();
	}
	pthread_mutex_unlock(&path_mutex);
}
