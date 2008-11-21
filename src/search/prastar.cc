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

PRAStar::PRAStarThread::PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, pthread_cond_t* con, pthread_mutex_t* mut, CompletionCounter* cc)
                                    : p(p),
                                      threads(threads),
                                      con(con),
                                      mut(mut),
                                      cc(cc) {}


PRAStar::PRAStarThread::~PRAStarThread(void) {}

/**
 * Run the search thread.
 */
void PRAStar::PRAStarThread::run(void){
	vector<const State *> *children;

        while(!p->has_path()){
          pthread_mutex_lock(mut);
          while (open.empty()){
            cout << "thread " << id << " has empty list" << endl;
            cc->complete();
            if (cc->is_complete()){
              p->done = true;
              cout << "thread " << id << " decided we're done" << endl;
              pthread_cond_broadcast(con);
            }
            else{
              cout << "thread " << id << " going to sleep" << endl;
              pthread_cond_wait(con, mut);
              cout << "thread " << id << " woke up" << endl;
            }
            if (p->done==true){
              pthread_mutex_unlock(mut);
              cout << "thread " << id << " quitting" << endl;
              return;
            }
            cc->uncomplete();
            cout << "thread " << id << " knocked CC down to " << cc->get_count() << endl;
          }
          cout << "thread " << id << " getting state" << endl;
          const State *s = open.take();
          pthread_mutex_unlock(mut);

          if (s->is_goal()) {
            p->set_path(s->get_path());
            pthread_mutex_lock(mut);
            p->done = true;
            pthread_cond_broadcast(con);
            pthread_mutex_unlock(mut);
            break;
          }
          
          children = p->expand(s);
          bool added = false;
          for (unsigned int i = 0; i < children->size(); i += 1) {
            const State *c = children->at(i);
            if (threads->at(c->hash()%p->n_threads)->closed.lookup(c) != NULL) {
              delete c;
              continue;
            }
            added = true;
            cout << "thread " << id << " added stuff to thread " << c->hash()%p->n_threads << endl;
            threads->at(c->hash()%p->n_threads)->closed.add(c);
            threads->at(c->hash()%p->n_threads)->open.add(c);
          }
          if (added){
            pthread_mutex_lock(mut);
            cout << "thread " << id << " waking everyone" << endl;
            pthread_cond_broadcast(con);
            pthread_mutex_unlock(mut);
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

void PRAStar::set_path(vector<const State *> *path)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL){
          this->path = path;
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

vector<const State *> *PRAStar::search(const State *init)
{
	vector<PRAStarThread *> threads;
	vector<PRAStarThread *>::iterator iter;
        pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);

        CompletionCounter cc = CompletionCounter(n_threads);
	pthread_cond_t c;
	pthread_mutex_t m;
        pthread_mutex_init(&m, NULL);
	pthread_cond_init(&c, NULL);

	for (unsigned int i = 0; i < n_threads; i += 1) {
		PRAStarThread *t = new PRAStarThread(this, &threads, &c, &m, &cc);
                t->id = i;
		threads.push_back(t);
	}

        cout << "thread " << init->hash()%n_threads << " got init" << endl;
        threads.at(init->hash()%n_threads)->open.add(init);
 	threads.at(init->hash()%n_threads)->closed.add(init);

	for (iter = threads.begin(); iter != threads.end(); iter++) {
        	(*iter)->start();
	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

	return path;
}
