/* -*- mode:linux -*- */
/**
 * \file pastar.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-11-02
 */

#include "util/thread.h"
#include "state.h"
#include "pastar.h"

class PAStarThread : public Thread {
public:
  PAStarThread() {}
  PAStarThread(PAStar *p) : p(p) {}
  PAStarThread(PAStar *p, pthread_cond_t* con, pthread_mutex_t* mut, CompletionCounter* cc) : p(p), con(con), mut(mut), cc(cc) {}

  virtual void run(void){
    vector<const State *> *children;
    
    while(!p->has_path()){
      pthread_mutex_lock(mut);
      while (p->open.empty()){
        cc->complete();
        if (cc->is_complete()){
          p->done = true;
          pthread_cond_broadcast(con);
        }
        else{
          pthread_cond_wait(con, mut);
        }
        if (p->done==true){
          pthread_mutex_unlock(mut);
          delete children;
          return;
        }
        cc->uncomplete();
      }
      const State *s = p->open.take();
      pthread_mutex_unlock(mut);

      const State *dup = p->closed.lookup(s);
      if (dup) {
	delete s;
	continue;
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
      bool added = false;
      for (unsigned int i = 0; i < children->size(); i += 1) {
        const State *c = children->at(i);
        if (p->closed.lookup(c) != NULL) {
          delete c;
          continue;
        }
        added = true;
        p->closed.add(c);
        p->open.add(c);
      }
      if (added){
        pthread_mutex_lock(mut);
        pthread_cond_broadcast(con);
        pthread_mutex_unlock(mut);
      }
    }
    
    delete children;
  }
  
private:
  PAStar *p;
  pthread_cond_t* con;
  pthread_mutex_t* mut;
  friend class PAStar;
  CompletionCounter *cc;
};


PAStar::PAStar(unsigned int n_threads) : n_threads(n_threads), path(NULL){
  done = false;
}

void PAStar::set_path(vector<const State *> *path)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL){
          this->path = path;
        }
        pthread_mutex_unlock(&mutex);
}

bool PAStar::has_path()
{
        bool ret;
        pthread_mutex_lock(&mutex);
 	ret = (path != NULL);
        pthread_mutex_unlock(&mutex);
        return ret;
}


/**
 * Perform a Parallel A* search.
 */
vector<const State *> *PAStar::search(const State *init)
{
 	open.add(init);
 	closed.add(init);
        pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);

        CompletionCounter cc = CompletionCounter(n_threads);
	pthread_cond_t c;
	pthread_mutex_t m;
        pthread_mutex_init(&m, NULL);
	pthread_cond_init(&c, NULL);

        unsigned int worker;
        vector<PAStarThread *> threads;
	vector<PAStarThread *>::iterator iter;
        for (worker=0; worker<n_threads; worker++) {
		PAStarThread *t = new PAStarThread(this, &c, &m, &cc);
		threads.push_back(t);
		t->start();
        }
	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

 	closed.delete_all_states();

 	return path;
}
