/**
 * \file prastar.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-11-19
 */

#include <assert.h>
#include <math.h>
#include <errno.h>

#include <vector>
#include <limits>

extern "C" {
#include "lockfree/include/atomic.h"
}

#include "util/msg_buffer.h"
#include "prastar.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

PRAStar::PRAStarThread::PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, CompletionCounter* cc)
	: p(p),
	  threads(threads),
	  cc(cc),
	  q_empty(true)
{
	out_qs.resize(threads->size(), NULL);
        completed = false;
        pthread_mutex_init(&mutex, NULL);
}

PRAStar::PRAStarThread::~PRAStarThread(void) {
	 vector<MsgBuffer<State*> *>::iterator i;
	for (i = out_qs.begin(); i != out_qs.end(); i++)
		if (*i)
			delete *i;
}

vector<State*> *PRAStar::PRAStarThread::get_queue(void)
{
	return &q;
}

pthread_mutex_t *PRAStar::PRAStarThread::get_mutex(void)
{
	return &mutex;
}

void PRAStar::PRAStarThread::post_send(void *t)
{

	PRAStarThread *thr = (PRAStarThread*) t;
	if (thr->completed) {
		thr->cc->uncomplete();
		thr->completed = false;
	}
	thr->q_empty = false;
}

void PRAStar::PRAStarThread::flush_sends(bool force)
{
	unsigned int i;
	for (i = 0; i < threads->size(); i += 1) {
		if (!out_qs[i])
			continue;
		if (out_qs[i]) {
			if (force)
				out_qs[i]->force_flush();
			else
				out_qs[i]->try_flush();
		}
	}
}

/**
 * Flush the queue
 */
void PRAStar::PRAStarThread::flush_queue(void)
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
				dup->update(c->get_parent(),
					    c->get_c(),
					    c->get_g());
				if (dup->is_open())
					open.see_update(dup);
				else
					open.add(dup);
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

void PRAStar::PRAStarThread::send_state(State *c, bool force)
{
	unsigned long hash = p->project->project(c);
	unsigned int dest_tid = threads->at(hash % p->n_threads)->get_id();
	bool self_add = dest_tid == this->get_id();

	if (self_add) {
		State *dup = closed.lookup(c);
		if (dup){
			if (dup->get_g() > c->get_g()) {
				dup->update(c->get_parent(),
					    c->get_c(),
					    c->get_g());
				if (dup->is_open())
					open.see_update(dup);
				else
					open.add(dup);
			}
			delete c;
		}
		else{
			open.add(c);
			closed.add(c);
		}
		return;
	}

	// not a self add
	//
	// Do a buffered send, unless the force flag is set, in which
	// case we can just sit on a lock because there is no work to
	// do anyway.
	if (!out_qs[dest_tid]) {
		pthread_mutex_t *lk = threads->at(dest_tid)->get_mutex();
		vector<State*> *qu = threads->at(dest_tid)->get_queue();
		out_qs[dest_tid] =
			new MsgBuffer<State*>(lk, qu,
					      post_send,
					      threads->at(dest_tid));
	}

	if (force)
		out_qs[dest_tid]->force_send(c);
	else
		out_qs[dest_tid]->try_send(c);

}

State *PRAStar::PRAStarThread::take(void){

	while (open.empty() || !q_empty) {
		flush_queue();

		// if there are no open nodes, might as well sit on
		// the lock.
		flush_sends(open.empty());

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
void PRAStar::PRAStarThread::run(void){
        vector<State *> *children = NULL;

        while(!p->is_done()){

		State *s = take();
		if (s == NULL)
			continue;

		if (s->get_f() >= p->bound.read()) {
			open.prune();
			continue;
		}
		if (s->is_goal()) {
			p->set_path(s->get_path());
		}

		children = p->expand(s);
		for (unsigned int i = 0; i < children->size(); i += 1) {
			State *c = children->at(i);
			send_state(c, false);
		}
        }

	if (children)
		delete children;

}


/************************************************************/


PRAStar::PRAStar(unsigned int n_threads)
	: n_threads(n_threads),
	  bound(fp_infinity),
	  project(NULL),
	  path(NULL){
        done = false;
}

PRAStar::~PRAStar(void) {
}

void PRAStar::set_done()
{
        pthread_mutex_lock(&mutex);
        done = true;
        pthread_mutex_unlock(&mutex);
}

bool PRAStar::is_done()
{
        bool ret;
        pthread_mutex_lock(&mutex);
        ret = done;
        pthread_mutex_unlock(&mutex);
        return ret;
}

void PRAStar::set_path(vector<State *> *p)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL ||
	    this->path->at(0)->get_g() > p->at(0)->get_g()){
		this->path = p;
		bound.set(p->at(0)->get_g());
        }
        pthread_mutex_unlock(&mutex);
}

bool PRAStar::has_path()
{
        bool ret;
        pthread_mutex_lock(&mutex);
        ret = (path != NULL);
        pthread_mutex_unlock(&mutex);
        return ret;
}

vector<State *> *PRAStar::search(Timer *timer, State *init)
{
        pthread_mutex_init(&mutex, NULL);
	project = init->get_domain()->get_projection();

        CompletionCounter cc = CompletionCounter(n_threads);

	threads.resize(n_threads, NULL);
        for (unsigned int i = 0; i < n_threads; i += 1) {
		PRAStarThread *t = new PRAStarThread(this, &threads, &cc);
		threads[i] = t;
        }

        threads.at(project->project(init)%n_threads)->open.add(init);

        for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->start();
        }

        for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
        }

        return path;
}
