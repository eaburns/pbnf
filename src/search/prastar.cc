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
                                      cc(cc) {
        completed = false;
}


PRAStar::PRAStarThread::~PRAStarThread(void) {}

void PRAStar::PRAStarThread::add(const State* s){
        pthread_mutex_lock(mut);
        if (open.empty() && completed){
          cc->uncomplete();
          completed = false;
        }
        open.add(s);
        closed.add(s);
        pthread_cond_broadcast(con);
        pthread_mutex_unlock(mut);
}

const State *PRAStar::PRAStarThread::take(void){
        pthread_mutex_lock(mut);
        if (open.empty()){
          cc->complete();
          completed = true;
          if (cc->is_complete()){
            p->done = true;
            pthread_mutex_unlock(mut);
            return NULL;
          }
          while (open.empty() && !p->done){
            pthread_cond_wait(con, mut);
          }
        }
        const State *ret = open.take();
        pthread_mutex_unlock(mut);
        return ret;
}

/**
 * Run the search thread.
 */
void PRAStar::PRAStarThread::run(void){
        vector<const State *> *children;

        while(!p->has_path()){
          const State *s = take();
          if (s == NULL){
            break;
          }

          if (s->is_goal()) {
            p->set_path(s->get_path());
            pthread_mutex_lock(mut);
            p->done = true;
            pthread_cond_broadcast(con);
            pthread_mutex_unlock(mut);
            break;
          }
          
          children = p->expand(s);
          for (unsigned int i = 0; i < children->size(); i += 1) {
            const State *c = children->at(i);
            if (threads->at(c->hash()%p->n_threads)->closed.lookup(c) != NULL) {
              delete c;
              continue;
            }
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
