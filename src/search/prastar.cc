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

#include "prastar.h"
#include "search.h"
#include "state.h"

using namespace std;

PRAStar::PRAStarThread::PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, CompletionCounter* cc)
                                    : p(p),
                                      threads(threads),
                                      cc(cc) {
        completed = false;
        pthread_mutex_init(&mutex, NULL);
}


PRAStar::PRAStarThread::~PRAStarThread(void) {
        delete q;
}

void PRAStar::PRAStarThread::add(State* s){
        pthread_mutex_lock(&mutex);
        if (open.empty() && completed){
          cc->uncomplete();
          completed = false;
        }
        q->push_back(s);
        pthread_mutex_unlock(&mutex);
}

State *PRAStar::PRAStarThread::take(void){
        if (open.empty() && q->empty()){
          cc->complete();
	  pthread_mutex_lock(&mutex);
          completed = true;
	  pthread_mutex_unlock(&mutex);
          if (cc->is_complete()){
            p->set_done();
            return NULL;
          }
          while (open.empty() && q->empty() && !p->is_done()){
          }
        }
	do{
	  if (pthread_mutex_trylock(&mutex) == 0){
	    for (unsigned int i = 0; 
		 i < q->size(); i += 1) {
	      State *c = q->at(i);
	      if (closed.lookup(c) != NULL) {
		delete c;
		continue;
	      }
	      open.add(c);
	    }
	    q->clear();
	    pthread_mutex_unlock(&mutex);
	  }
	}
	while (open.empty() && !p->is_done());
	State *ret;
	if (!open.empty() && !p->is_done()){
	  ret = open.take();
	}
	else{
	  ret = NULL;
	}
        return ret;
}

/**
 * Run the search thread.
 */
void PRAStar::PRAStarThread::run(void){
        vector<State *> *children;
	q = new vector<State *>();

        while(!p->has_path()){
          State *s = take();
          if (s == NULL){
            break;
          }
	  State *dup = closed.lookup(s);
	  if (dup && dup->get_g() < s->get_g()) {
	    delete s;
	    continue;
	  }

	  closed.add(s);

          if (s->is_goal()) {
            p->set_path(s->get_path());
            break;
          }
          
          children = p->expand(s);
          for (unsigned int i = 0; i < children->size(); i += 1) {
            State *c = children->at(i);
            threads->at(c->hash()%p->n_threads)->add(c);
          }
        }

        delete children;
}


/************************************************************/


PRAStar::PRAStar(unsigned int n_threads) 
               : n_threads(n_threads),
                 path(NULL) {
        done = false;
}

PRAStar::~PRAStar(void) {}

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

void PRAStar::set_path(vector<State *> *path)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL || 
	    this->path->back()->get_g() > path->back()->get_g()){
          this->path = path;
	  done = true;
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

vector<State *> *PRAStar::search(State *init)
{
        pthread_mutex_init(&mutex, NULL);

        CompletionCounter cc = CompletionCounter(n_threads);

        for (unsigned int i = 0; i < n_threads; i += 1) {
          PRAStarThread *t = new PRAStarThread(this, &threads, &cc);
          threads.push_back(t);
        }

        threads.at(init->hash()%n_threads)->open.add(init);

        for (iter = threads.begin(); iter != threads.end(); iter++) {
          (*iter)->start();
        }

        for (iter = threads.begin(); iter != threads.end(); iter++) {
          (*iter)->join();
          delete *iter;
        }

        return path;
}
