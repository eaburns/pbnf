 /**
 * \file wprastar.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-03-19
 */

#include <assert.h>
#include <math.h>
#include <errno.h>

#include <vector>
#include <limits>

#include "wprastar.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

wPRAStar::wPRAStarThread::wPRAStarThread(wPRAStar *p, vector<wPRAStarThread *> *threads, CompletionCounter* cc)
	: p(p),
	  threads(threads),
	  cc(cc),
	  q_empty(true)
{
        completed = false;
        pthread_mutex_init(&mutex, NULL);
}


wPRAStar::wPRAStarThread::~wPRAStarThread(void) {
}

void wPRAStar::wPRAStarThread::add(State* c, bool self_add){
	if (self_add){
		State *dup = closed.lookup(c);
		if (dup){
			if (dup->get_g() > c->get_g()) {
				fp_type old_g = dup->get_g();
				fp_type parent_g = c->get_g() - c->get_c();

				dup->update(c->get_parent(), c->get_c(), c->get_g());
				if (dup->is_open())
					open.see_update(dup);
				else if (!p->dd || old_g > parent_g + ((p->weight * c->get_c()) / fp_one)) {
					//  Wheeler's dup dropping
					open.add(dup);
				}
			}
			delete c;
		}
		else{
			open.add(c);
			closed.add(c);
		}

		return;
	}
        pthread_mutex_lock(&mutex);
        if (completed){
		cc->uncomplete();
		completed = false;
        }
        q.push_back(c);
	q_empty = false;
        pthread_mutex_unlock(&mutex);
}

/**
 * Flush the queue
 */
void wPRAStar::wPRAStarThread::flush_queue(void)
{
	// wait for either completion or more nodes to expand
	if (open.empty()) {
		pthread_mutex_lock(&mutex);
	} else if (pthread_mutex_trylock(&mutex) == EBUSY) {
		return;
	}
	if (q_empty) {
		if (!open.empty()) {
			pthread_mutex_unlock(&mutex);
			return;
		}
		completed = true;
		cc->complete();

		// busy wait
		pthread_mutex_unlock(&mutex);
		while (q_empty && !cc->is_complete() && !p->is_done())
			;
		pthread_mutex_lock(&mutex);

		// we are done, just return
		if (cc->is_complete()) {
			assert(q_empty);
			pthread_mutex_unlock(&mutex);
			return;
		}
	}

	// got some stuff on the queue, lets do duplicate detection
	// and add stuff to the open list
	for (unsigned int i = 0; i < q.size(); i += 1) {
		State *c = q[i];
		State *dup = closed.lookup(c);
		if (dup){
			if (dup->get_g() > c->get_g()) {
				fp_type old_g = dup->get_g();
				fp_type parent_g = c->get_g() - c->get_c();
				dup->update(c->get_parent(), c->get_c(), c->get_g());
				if (dup->is_open())
					open.see_update(dup);
				else if (!p->dd || old_g > parent_g + ((p->weight * c->get_c()) / fp_one)) {
					// Wheeler's dup dropping
					open.add(dup);
				}
			}
			delete c;
		}
		else{
			open.add(c);
			closed.add(c);
		}
	}
	q.clear();
	q_empty = true;
	pthread_mutex_unlock(&mutex);
}

State *wPRAStar::wPRAStarThread::take(void){
	while (open.empty() || !q_empty) {
		flush_queue();
		if (cc->is_complete()){
			p->set_done();
			return NULL;
		}
        }

	State *ret = NULL;
	if (!p->is_done())
		ret = open.take();

        return ret;
}

/**
 * Run the search thread.
 */
void wPRAStar::wPRAStarThread::run(void){
        vector<State *> *children = NULL;

        while(!p->is_done()){
		State *s = take();
		if (s == NULL)
			continue;

		if (s->get_f_prime() >= p->bound.read()) {
			open.prune();
		}
		if (p->weight * s->get_f() >= p->bound.read()) {
			continue;
		}
		if (s->is_goal()) {
			p->set_path(s->get_path());
		}

		children = p->expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			State *c = children->at(i);
			unsigned long hash =
				p->use_abstraction
				? p->project->project(c)
				: c->hash();
			unsigned int dest_tid = threads->at(hash % p->n_threads)->get_id();
			bool self_add = dest_tid == this->get_id();
			threads->at(dest_tid)->add(c, self_add);
		}
        }

	if (children)
		delete children;

}


/************************************************************/


wPRAStar::wPRAStar(unsigned int n_threads, bool d, bool abst)
	: n_threads(n_threads),
	  bound(fp_infinity),
	  project(NULL),
	  path(NULL),
	  dd(d),
	  use_abstraction(abst){
        done = false;
}


wPRAStar::wPRAStar(unsigned int n_threads, fp_type bound, bool d, bool abst)
	: n_threads(n_threads),
          bound(bound),
	  project(NULL),
	  path(NULL),
	  dd(d),
	  use_abstraction(abst) {
        done = false;
}

wPRAStar::~wPRAStar(void) {
}

void wPRAStar::set_done()
{
        pthread_mutex_lock(&mutex);
        done = true;
        pthread_mutex_unlock(&mutex);
}

bool wPRAStar::is_done()
{
        bool ret;
        pthread_mutex_lock(&mutex);
        ret = done;
        pthread_mutex_unlock(&mutex);
        return ret;
}

void wPRAStar::set_path(vector<State *> *p)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL ||
	    this->path->at(0)->get_g() > p->at(0)->get_g()){
		this->path = p;
		bound.set(p->at(0)->get_g());
        }
        pthread_mutex_unlock(&mutex);
}

bool wPRAStar::has_path()
{
        bool ret;
        pthread_mutex_lock(&mutex);
        ret = (path != NULL);
        pthread_mutex_unlock(&mutex);
        return ret;
}

vector<State *> *wPRAStar::search(Timer *t, State *init)
{
        pthread_mutex_init(&mutex, NULL);
	project = init->get_domain()->get_projection();
	weight = init->get_domain()->get_heuristic()->get_weight();

        CompletionCounter cc = CompletionCounter(n_threads);

	threads.resize(n_threads, NULL);
        for (unsigned int i = 0; i < n_threads; i += 1)
		threads.at(i) = new wPRAStarThread(this, &threads, &cc);

	if (use_abstraction)
		threads.at(project->project(init)%n_threads)->open.add(init);
	else
		threads.at(init->hash() % n_threads)->open.add(init);

        for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->start();
        }

        for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
        }

        return path;
}
