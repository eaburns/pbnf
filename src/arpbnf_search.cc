/**
 * \file arpbnf_search.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-29
 */

#include <assert.h>
#include <math.h>

#include <limits>
#include <vector>
#include <algorithm>

#include "arpbnf_search.h"
#include "search.h"
#include "state.h"
#include "util/timer.h"
#include "util/sync_solution_stream.h"

using namespace std;
using namespace ARPBNF;

ARPBNFSearch::ARPBNFThread::ARPBNFThread(NBlockGraph *graph, ARPBNFSearch *search)
	: graph(graph), search(search), set_hot(false)
{
}


ARPBNFSearch::ARPBNFThread::~ARPBNFThread(void) {}

/**
 * Run the search thread.
 */
void ARPBNFSearch::ARPBNFThread::run(void)
{
	vector<State *> *path;
	NBlock *n = NULL;

	do {
	next:
		n = graph->next_nblock(n, !set_hot);
		set_hot = false;
		if (n) {
			expansions = 0;
			path = search_nblock(n);

			if (path) {
				if (search->set_path(path)) {
					graph->free_nblock(n);
					n = NULL;
					graph->call_for_resort(&search->nincons);
					goto next;
				}
			}
		} else if (search->nincons.read() != 0) {
			if (search->move_to_next_weight()) {
				graph->call_for_resort(&search->nincons);
				goto next;
			}
		}
	} while (n);

	graph->set_done();
}

/**
 * Search a single NBlock.
 */
vector<State *> *ARPBNFSearch::ARPBNFThread::search_nblock(NBlock *n)
{
	vector<State *> *path = NULL;
	OpenList *open = &n->open;

	while (!open->empty() && !should_switch(n) && !graph->needs_resort()) {
		State *s = open->take();

		if (s->get_f() >= search->bound.read())
			continue;

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;

		vector<State *> *children = search->expand(s);
		vector<State *>::iterator iter;

 		for (iter = children->begin(); iter != children->end(); iter++) {
			State *ch = *iter;
			// First check if we can prune!
			if (ch->get_f() >= search->bound.read()) {
				delete ch;
				continue;
			}
			vector<State *> *path = process_child(ch);
			if (path) {
				delete children;
				return path;
			}
		}
		delete children;
	}

	return path;
}

/**
 * Process a child state.
 *
 * \return A path if the child was a goal state... maybe we can prune
 *         more on this.
 */
vector<State *> *ARPBNFSearch::ARPBNFThread::process_child(State *ch)
{
	unsigned int block = search->project->project(ch);
	PQOpenList<State::PQOpsFPrime> *copen = &graph->get_nblock(block)->open;
	ClosedList *cclosed = &graph->get_nblock(block)->closed;
	InconsList *cincons = &graph->get_nblock(block)->incons;
	State *dup = cclosed->lookup(ch);

	if (dup) {
		if (dup->get_g() > ch->get_g()) {
			dup->update(ch->get_parent(), ch->get_g());
			if (dup->is_open()) {
				copen->see_update(dup);
			} else {
				if (search->incons && !search->final_weight) {
					if (cincons->empty())
						search->nincons.inc();
					cincons->add(dup);
				} else {
					copen->add(dup);
				}
			}
		}
		delete ch;
	} else {
		cclosed->add(ch);
		if (ch->is_goal())
			return ch->get_path();
		copen->add(ch);
	}

	return NULL;
}


/**
 * Test the graph to see if we should switch to a new NBlock.
 * \param n The current NBlock.
 *
 * \note We should make this more complex... we should also check our
 *       successor NBlocks.
 */
bool ARPBNFSearch::ARPBNFThread::should_switch(NBlock *n)
{
	bool ret;

	if (expansions < search->min_expansions)
		return false;

	expansions = 0;

	fp_type free = graph->best_val();
	fp_type cur = n->open.get_best_val();
	NBlock *best_scope = graph->best_in_scope(n);

	if (best_scope) {
		fp_type scope = best_scope->open.get_best_val();

		ret = free < cur || scope < cur;
		if (!ret) {
			graph->wont_release(n);
		} else if (scope < free) {
			graph->set_hot(best_scope);
			set_hot = true;
		}
	} else {
		ret = free < cur;
	}

	return ret;
}


/*****************************************************************************/
/*****************************************************************************/


ARPBNFSearch::ARPBNFSearch(unsigned int n_threads,
			   unsigned int min_e,
			   bool use_incons,
			   vector<double> *w)
	: n_threads(n_threads),
	  incons(use_incons),
	  project(NULL),
	  bound(fp_infinity),
	  graph(NULL),
	  min_expansions(min_e),
	  weights(w),
	  next_weight(1),
	  domain(NULL),
	  final_weight(false),
	  nincons(0)
{
	pthread_mutex_init(&wmutex, NULL);
}


ARPBNFSearch::~ARPBNFSearch(void)
{
	if (graph)
		delete graph;
}


vector<State *> *ARPBNFSearch::search(Timer *timer, State *initial)
{
	solutions = new SyncSolutionStream(timer, 0.0001);
	domain = initial->get_domain();
	project = domain->get_projection();

	vector<ARPBNFSearch::ARPBNFThread*> threads;
	vector<ARPBNFSearch::ARPBNFThread*>::iterator iter;

	graph = new NBlockGraph(project, initial);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		ARPBNFThread *t = new ARPBNFThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

	return solutions->get_best_path();
}

bool ARPBNFSearch::__move_to_next_weight(void)
{
	final_sol_weight = weights->at(next_weight - 1);

	if (weights->at(next_weight - 1) != 1.0) {
		double nw = 1.0;
		if (next_weight < weights->size()) {
			nw = weights->at(next_weight);
			next_weight += 1;
		} else {
			cerr << "Final weight is not 1.0, using 1.0" << endl;
		}

		domain->get_heuristic()->set_weight(nw);
		if (nw == 1.0 || next_weight == weights->size())
			final_weight = true;

		return true;
	}

	return false;
}

bool ARPBNFSearch::move_to_next_weight(void)
{
	bool ret;

	pthread_mutex_lock(&wmutex);
	ret = __move_to_next_weight();
	pthread_mutex_unlock(&wmutex);

	return ret;
}

/**
 * Set an incumbant solution.
 *
 * If this function returns true than the calling thread must call for
 * a resort.
 */
bool ARPBNFSearch::set_path(vector<State *> *p)
{
	bool ret = false;
	assert(solutions);

	pthread_mutex_lock(&wmutex);

	if (bound.read() <= p->at(0)->get_g()) {
		pthread_mutex_unlock(&wmutex);
		return false;
	}

	solutions->see_solution(p, get_generated(), get_expanded());
	bound.set(p->at(0)->get_g());

#if !defined(NDEBUG)
	cout << "Solution of cost " << p->at(0)->get_g() / fp_one
	     << " found at weight " << weights->at(next_weight - 1)
	     << endl;
#endif	// !NDEBUG

	ret = __move_to_next_weight();

	pthread_mutex_unlock(&wmutex);

	return ret;
}

/**
 * Output extra "key: value" pairs.
 * keys should not have spaces in their names!
 */
void ARPBNFSearch::output_stats(void)
{
	cout << "total-nblocks: " << project->get_num_nblocks() << endl;
	cout << "created-nblocks: " << graph->get_ncreated_nblocks() << endl;
	cout << "final-sol-weight: " << final_sol_weight << endl;

	if (solutions)
		solutions->output(cout);
}
