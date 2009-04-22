/**
 * \file wpbnf_search.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-04-18
 */

#include <assert.h>
#include <math.h>

#include <limits>
#include <vector>
#include <algorithm>

#include "opbnf_search.h"
#include "search.h"
#include "state.h"
#include "util/timer.h"
#include "util/cumulative_ave.h"

using namespace std;
using namespace OPBNF;

#define MIN_M 1
#define MAX_INT std::numeric_limits<int>::max()

OPBNFSearch::PBNFThread::PBNFThread(NBlockGraph *graph, OPBNFSearch *search)
	: graph(graph), search(search), set_hot(false) {
	next_best = 0.0;
}


OPBNFSearch::PBNFThread::~PBNFThread(void) {}


/**
 * Run the search thread.
 */
void OPBNFSearch::PBNFThread::run(void)
{
	vector<State *> *path;
	NBlock *n = NULL;

	do {
		n = graph->next_nblock(n, !set_hot, search->bound.read());

		if ((search->b * graph->get_f_min()) > search->bound.read())
			break;

		set_hot = false;
		if (n) {
			expansions = 0;
			path = search_nblock(n);

			if (path)
				search->set_path(path);
		}
	} while (!search->done && n);

	search->done = true;
	graph->set_done();
}

/**
 * Search a single NBlock.
 */
vector<State *> *OPBNFSearch::PBNFThread::search_nblock(NBlock *n)
{
	vector<State *> *path = NULL;
	PQOpenList<State::PQOpsFPrime> *open_fp = &n->open_fp;
	PQOpenList<State::PQOpsF> *open_f = &n->open_f;
//	ClosedList *closed = &n->closed;

	while (!search->done && !open_fp->empty() && !should_switch(n)) {
		// If the best f value in this nblock is bad, prune everything.
		if (search->b * open_f->get_best_val() >= search->bound.read()) {
			open_f->prune();
			open_fp->prune();
			break;
		}

		State *s;
		if(open_fp->get_best_val() < search->bound.read()){
			s = open_fp->take();
			open_f->remove(s);
		}
		else{
			s = open_f->take();
			open_fp->remove(s);
		}

		// If the individual f value is bad, prune the single node.
		if (search->b * s->get_f() >= search->bound.read())
			continue;

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;

		vector<State *> *children = search->expand(s);
		vector<State *>::iterator iter;

 		for (iter = children->begin(); iter != children->end(); iter++) {
			if (search->b * (*iter)->get_f() >= search->bound.read()) {
				delete *iter;
				continue;
			}
			unsigned int block = search->project->project(*iter);
			PQOpenList<State::PQOpsFPrime> *next_open_fp = &graph->get_nblock(block)->open_fp;
			PQOpenList<State::PQOpsF> *next_open_f = &graph->get_nblock(block)->open_f;
			ClosedList *next_closed = &graph->get_nblock(block)->closed;
			State *dup = next_closed->lookup(*iter);
			if (dup) {
				if (dup->get_g() > (*iter)->get_g()) {
					dup->update((*iter)->get_parent(),
						    (*iter)->get_c(),
						    (*iter)->get_g());
					if (dup->is_open()) {
						next_open_fp->see_update(dup);
						next_open_f->see_update(dup);
					} else {
						next_open_fp->add(dup);
						next_open_f->add(dup);
					}
				}
				delete *iter;
			} else {
				next_closed->add(*iter);
				if ((*iter)->is_goal()) {
					path = (*iter)->get_path();
					delete children;
					return path;
				}
				next_open_fp->add(*iter);
				next_open_f->add(*iter);
			}
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
bool OPBNFSearch::PBNFThread::should_switch(NBlock *n)
{
	bool ret;

	if (next_best == 0.0 || graph->best_free_fp_val() != 0.0){
		if (expansions < search->min_expansions)
			return false;
	}
	else{
		return n->open_fp.get_best_val() > next_best;
	}

	expansions = 0;

	fp_type bound = search->bound.read();

	NBlock *best_scope = graph->best_in_scope(n, bound);
	NBlock *free_fp = graph->next_nblock_fp_peek();
	NBlock *free_f = graph->next_nblock_f_peek();
	bool free_exist = free_fp != NULL;
	bool free = free_exist && (NBlock::better(free_fp, n, bound)
				   || NBlock::better(free_f, n, bound));
	if (best_scope) {
		bool scope = NBlock::better(best_scope, n, bound);
		ret = free || scope;
		if (!ret)
			graph->wont_release(n);
		else if (scope
			 && (!free_exist
			     || (NBlock::better(best_scope, free_fp, bound)
				 && NBlock::better(best_scope, free_f, bound)))) {
			graph->set_hot(best_scope, search->bound.read());
			set_hot = true;
		}
	} else {
		ret = free;
	}

	return ret;
}


/************************************************************/
/************************************************************/
/************************************************************/


OPBNFSearch::OPBNFSearch(unsigned int n_threads,
			 unsigned int min_e)
	: n_threads(n_threads),
	  project(NULL),
	  path(NULL),
	  bound(fp_infinity),
	  done(false),
	  graph(NULL),
	  min_expansions(min_e)
{
	pthread_mutex_init(&path_mutex, NULL);
}


OPBNFSearch::~OPBNFSearch(void)
{
	if (graph)
		delete graph;
}


vector<State *> *OPBNFSearch::search(Timer *t, State *initial)
{
	project = initial->get_domain()->get_projection();

	vector<PBNFThread *> threads;
	vector<PBNFThread *>::iterator iter;

	graph_timer.start();
	graph = new NBlockGraph(project, initial);
	graph_timer.stop();

	b = fp_type(1.0);
	weight = initial->get_domain()->get_heuristic()->get_weight();

	for (unsigned int i = 0; i < n_threads; i += 1) {
		PBNFThread *t = new PBNFThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}
	return path;
}


/**
 * Set an incumbant solution.
 */
void OPBNFSearch::set_path(vector<State *> *p)
{
	pthread_mutex_lock(&path_mutex);
	assert(p->at(0)->get_g() == p->at(0)->get_f());
	if (p && bound.read() > p->at(0)->get_g()) {
		this->path = p;
		bound.set(p->at(0)->get_g());

		if ((b * graph->get_f_min()) > p->at(0)->get_g()){
			cout << "terminated based on f_min!!!" << endl;
			done = true;
		}
	}
	pthread_mutex_unlock(&path_mutex);
}

void OPBNFSearch::output_stats(void)
{
	cout << "nblock-graph-creation-time: " << graph_timer.get_wall_time() << endl;
	cout << "total-nblocks: " << project->get_num_nblocks() << endl;
	cout << "created-nblocks: " << graph->get_ncreated_nblocks() << endl;
}
