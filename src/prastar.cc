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

#include "util/timer.h"
#include "util/mutex.h"
#include "util/msg_buffer.h"
#include "util/sync_solution_stream.h"
#include "prastar.h"
#include "projection.h"
#include "search.h"
#include "state.h"

using namespace std;

PRAStar::PRAStarThread::PRAStarThread(PRAStar *p,
				      vector<PRAStarThread *> *threads,
				      CompletionCounter* cc)
	: p(p),
	  threads(threads),
	  cc(cc),
	  q_empty(true)
{
	time_spinning = 0;
	out_qs.resize(threads->size(), NULL);
        completed = false;
}

PRAStar::PRAStarThread::~PRAStarThread(void)
{
	vector<MsgBuffer<State*> *>::iterator i;
	for (i = out_qs.begin(); i != out_qs.end(); i++)
		if (*i)
			delete *i;
}

vector<State*> *PRAStar::PRAStarThread::get_queue(void)
{
	return &q;
}

Mutex *PRAStar::PRAStarThread::get_mutex(void)
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

bool PRAStar::PRAStarThread::flush_sends(void)
{
	unsigned int i;
	bool has_sends = false;
	for (i = 0; i < threads->size(); i += 1) {
		if (!out_qs[i])
			continue;
		if (out_qs[i]) {
			out_qs[i]->try_flush();
			if (!out_qs[i]->is_empty())
				has_sends = true;
		}
	}

	return has_sends;
}

/**
 * Flush the queue
 */
void PRAStar::PRAStarThread::flush_receives(bool has_sends)
{
	// wait for either completion or more nodes to expand
	if (open.empty() || !p->async)
		mutex.lock();
	else if (!mutex.try_lock()) // asynchronous
		return;

	if (q_empty && !has_sends) {
		if (!open.empty()) {
			mutex.unlock();
			return;
		}
		completed = true;
		cc->complete();

		// busy wait
		mutex.unlock();
		while (q_empty && !cc->is_complete() && !p->is_done())
			;
		mutex.lock();

		// we are done, just return
		if (cc->is_complete()) {
			assert(q_empty);
			mutex.unlock();
			return;
		}
	}

	// got some stuff on the queue, lets do duplicate detection
	// and add stuff to the open list
	for (unsigned int i = 0; i < q.size(); i += 1) {
		State *c = q[i];
		if (c->get_f() >= p->bound.read()) {
			delete c;
			continue;
		}
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
	mutex.unlock();
}

void PRAStar::PRAStarThread::do_async_send(unsigned int dest_tid, State *c)
{
	if (!out_qs[dest_tid]) {
		Mutex *lk = threads->at(dest_tid)->get_mutex();
		vector<State*> *qu = threads->at(dest_tid)->get_queue();
		out_qs[dest_tid] =
			new MsgBuffer<State*>(lk, qu,
					      post_send,
					      threads->at(dest_tid));
	}

	out_qs[dest_tid]->try_send(c);
}

void PRAStar::PRAStarThread::do_sync_send(unsigned int dest_tid, State *c)
{
	PRAStarThread *dest = threads->at(dest_tid);

	dest->get_mutex()->lock();
	dest->get_queue()->push_back(c);
	post_send(dest);
	dest->get_mutex()->unlock();
}

void PRAStar::PRAStarThread::send_state(State *c)
{
	unsigned long hash =
		p->use_abstraction
		? p->project->project(c)
		: c->hash();
	unsigned int dest_tid = threads->at(hash % p->n_threads)->get_id();
	bool self_add = dest_tid == this->get_id();

	assert (p->n_threads != 1 || self_add);

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
	if (p->async)
		do_async_send(dest_tid, c);
	else
		do_sync_send(dest_tid, c);
}

State *PRAStar::PRAStarThread::take(void)
{
	Timer t;
	bool entered_loop = false;

	bool has_sends = flush_sends();

	t.start();
	while (open.empty() || !q_empty) {
		entered_loop = true;

		has_sends = flush_sends();
		flush_receives(has_sends);

		if (cc->is_complete()){
			p->set_done();
			return NULL;
		}
        }
	t.stop();
	if (entered_loop)
		time_spinning += t.get_wall_time();

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
			if (c->get_f() < p->bound.read())
				send_state(c);
			else
				delete c;
		}
		delete children;
        }
}


/************************************************************/


PRAStar::PRAStar(unsigned int n_threads, bool use_abst, bool asy)
	: n_threads(n_threads),
	  bound(fp_infinity),
	  project(NULL),
	  use_abstraction(use_abst),
	  async(asy)
{
        done = false;
}

PRAStar::~PRAStar(void)
{
        for (iter = threads.begin(); iter != threads.end(); iter++) {
		if (*iter)
			delete (*iter);
	}
}

void PRAStar::set_done()
{
	mutex.lock();
        done = true;
	mutex.unlock();
}

bool PRAStar::is_done()
{
        return done;
}

void PRAStar::set_path(vector<State *> *p)
{
	fp_type b, oldb;

	assert(solutions);

	solutions->see_solution(p, get_generated(), get_expanded());
	b = solutions->get_best_path()->at(0)->get_g();

	// CAS in our new solution bound if it is still indeed better
	// than the previous bound.
	do {
		oldb = bound.read();
		if (oldb <= b)
			return;
	} while (bound.cmp_and_swap(oldb, b) != oldb);
}

vector<State *> *PRAStar::search(Timer *timer, State *init)
{
	solutions = new SyncSolutionStream(timer, 0.0001);
	project = init->get_domain()->get_projection();

        CompletionCounter cc = CompletionCounter(n_threads);

	threads.resize(n_threads, NULL);
        for (unsigned int i = 0; i < n_threads; i += 1)
                threads.at(i) = new PRAStarThread(this, &threads, &cc);

	if (use_abstraction)
		threads.at(project->project(init)%n_threads)->open.add(init);
	else
		threads.at(init->hash() % n_threads)->open.add(init);

        for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->start();
        }

        for (iter = threads.begin(); iter != threads.end(); iter++)
		(*iter)->join();

        return solutions->get_best_path();
}

void PRAStar::output_stats(void)
{
	time_spinning = 0.0;
	max_open_size = 0;
	avg_open_size = 0;
        for (iter = threads.begin(); iter != threads.end(); iter++) {
		time_spinning += (*iter)->time_spinning;
		avg_open_size += (*iter)->open.get_avg_size();
		if ((*iter)->open.get_max_size() > max_open_size)
			max_open_size = (*iter)->open.get_max_size();
        }
	avg_open_size /= n_threads;

	if (solutions)
		solutions->output(cout);

	cout << "total-time-acquiring-locks: "
	     << Mutex::get_total_lock_acquisition_time() << endl;
	cout << "average-time-acquiring-locks: "
	     << Mutex::get_total_lock_acquisition_time() / n_threads
	     << endl;
	cout << "total-time-waiting: " << time_spinning << endl;
	cout << "average-time-waiting: "
	     << time_spinning / n_threads << endl;
	cout << "average-open-size: " << avg_open_size << endl;
	cout << "max-open-size: " << max_open_size << endl;
}
