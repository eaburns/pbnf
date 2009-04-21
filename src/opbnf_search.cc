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

AtomicInt OPBNFSearch::min_expansions(MIN_M);

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
		if(graph->next_nblock_fp_value() < search->bound.read()){
			n = graph->next_nblock_fp(n, !set_hot);
		}
		else{
			cout << "that other thing" << endl;
			n = graph->next_nblock_f(n, !set_hot);
		}

		if ((search->b * graph->get_f_min()) > search->bound.read())
			break;

		if (n && search->dynamic_m){
			next_best = graph->best_free_fp_val();
		}

		set_hot = false;
		if (n) {
			expansions = 0;
			exp_this_block = 0;
			path = search_nblock(n);

			if (path)
				search->set_path(path);
			ave_exp_per_nblock.add_val(exp_this_block);
		}
	} while (!search->done && n);

	search->done = true;
	graph->set_done();
}

/**
 * Get the average number of expansions per-nblock.
 */
fp_type OPBNFSearch::PBNFThread::get_ave_exp_per_nblock(void)
{
	return ave_exp_per_nblock.read();
}

/**p
 * Get the average size of open lists.
 */
fp_type OPBNFSearch::PBNFThread::get_ave_open_size(void)
{
	return ave_open_size.read();
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
		if(open_fp->get_best_val() >= search->bound.read()){
			s = open_fp->take();
			open_f->remove(s);
		}
		else{
			s = open_f->take();
			open_fp->remove(s);
		}
		ave_open_size.add_val(open_fp->size());

		// If the individual f value is bad, prune the single node.
		if (search->b * s->get_f() >= search->bound.read())
			continue;

		if (s->is_goal()) {
			path = s->get_path();
			break;
		}

		expansions += 1;
		exp_this_block += 1;

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
					ave_open_size.add_val(next_open_fp->size());
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
				ave_open_size.add_val(next_open_fp->size());
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
		if (expansions < search->min_expansions.read())
			return false;
	}
	else{
		return n->open_fp.get_best_val() > next_best;
	}

	expansions = 0;

	fp_type free_fp = graph->next_nblock_fp_value();
	fp_type cur_fp = n->open_fp.get_best_val();
	fp_type free_f = graph->next_nblock_f_value();
	fp_type cur_f = n->open_f.get_best_val();

	NBlock *best_scope = graph->best_in_scope(n);
	if (best_scope) {
		fp_type scope = best_scope->open_fp.get_best_val();

		ret = free_fp < cur_fp || scope < cur_fp;
		if (!ret)
			graph->wont_release(n);
		else if (scope < free_fp) {
			graph->set_hot(best_scope);
			set_hot = true;
		}
	} else {
		if(cur_fp < search->bound.read() || free_fp < search->bound.read()){
			ret = free_fp < cur_fp;
		}
		else{
			ret = free_f < cur_f;
		}
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
	  graph(NULL)
{
	pthread_mutex_init(&path_mutex, NULL);
	if (min_e == 0){
		dynamic_m = true;
		OPBNFSearch::min_expansions = AtomicInt(MIN_M);
	}
	else{
		dynamic_m = false;
		OPBNFSearch::min_expansions = AtomicInt(min_e);
	}
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
	fp_type sum = 0.0;
	unsigned int num = 0;
	fp_type osum = 0.0;
	unsigned int onum = 0;

	graph_timer.start();
	graph = new NBlockGraph(project, initial);
	graph_timer.stop();

	b = fp_type(1);
	weight = initial->get_domain()->get_heuristic()->get_weight();

	for (unsigned int i = 0; i < n_threads; i += 1) {
		PBNFThread *t = new PBNFThread(graph, this);
		threads.push_back(t);
		t->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();

		fp_type ave = (*iter)->get_ave_exp_per_nblock();
		if (ave != 0) {
			sum += ave;
			num += 1;
		}
		fp_type oave = (*iter)->get_ave_open_size();
		if (oave != 0) {
			osum += oave;
			onum += 1;
		}

		delete *iter;
	}
	if (num == 0)
		cout << "expansions-per-nblock: -1" << endl;
	else
		cout << "expansions-per-nblock: " << sum / num << endl;
	if (onum == 0)
		cout << "avg-open-list-size: -1" << endl;
	else
		cout << "avg-open-list-size: " << osum / onum << endl;

	cout << "nblock-graph-creation-time: " << graph_timer.get_wall_time() << endl;

	cout << "total-nblocks: " << project->get_num_nblocks() << endl;
	cout << "created-nblocks: " << graph->get_ncreated_nblocks() << endl;

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

		cout << "f_min: " << graph->get_f_min() << endl;
		if ((b * graph->get_f_min()) > p->at(0)->get_g()){
			done = true;
		}
	}
	pthread_mutex_unlock(&path_mutex);
}