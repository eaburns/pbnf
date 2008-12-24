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
	: graph(graph), search(search), set_hot(false) {}


PBNFSearch::PBNFThread::~PBNFThread(void) {}


/**
 * Run the search thread.
 */
void PBNFSearch::PBNFThread::run(void)
{
	vector<const State *> *path;
	NBlock *n = NULL;

	do {
		n = graph->next_nblock(n, !set_hot);
		set_hot = false;
		if (n) {
			expansions = 0;
			exp_this_block = 0;
			path = search_nblock(n);

			if (path)
				search->set_path(path);
			ave_exp_per_nblock.add_val(exp_this_block);
		}
	} while (n);

	graph->set_done();
}

/**
 * Get the average number of expansions per-nblock.
 */
float PBNFSearch::PBNFThread::get_ave_exp_per_nblock(void)
{
	return ave_exp_per_nblock.read();
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
		if (dup && dup->get_g() <= s->get_g()) {
			delete s;
			continue;
		}

		closed->add(s);

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;
		exp_this_block += 1;

		vector<const State *> *children = search->expand(s);
		vector<const State *>::iterator iter;

 		for (iter = children->begin(); iter != children->end(); iter++) {
			if ((*iter)->get_f() >= search->bound.read()) {
				delete *iter;
				continue;
			}
			unsigned int block = search->project->project(*iter);
			OpenList *next_open = &graph->get_nblock(block)->open;
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
		else if (scope < free) {
			graph->set_hot(best_scope);
			set_hot = true;
		}
	} else {
		ret = free < cur;
	}

	return ret;
}


/************************************************************/
/************************************************************/
/************************************************************/


PBNFSearch::PBNFSearch(unsigned int n_threads,
		       unsigned int min_expansions,
		       bool detect_livelocks)
	: n_threads(n_threads),
	  project(NULL),
	  path(NULL),
	  bound(INFINITY),
	  detect_livelocks(detect_livelocks),
	  min_expansions(min_expansions)
{
	pthread_mutex_init(&path_mutex, NULL);
}


PBNFSearch::~PBNFSearch(void) {}


vector<const State *> *PBNFSearch::search(const State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<PBNFThread *> threads;
	vector<PBNFThread *>::iterator iter;
	float sum = 0.0;
	unsigned int num;

	NBlockGraph *graph = new NBlockGraph(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		PBNFThread *t = new PBNFThread(graph, this);
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
