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
  PAStarThread(PAStar *p, pthread_mutex_t* mut, CompletionCounter* cc) : p(p), mut(mut), cc(cc) {}

  virtual void run(void){
    vector<const State *> *children = NULL;
    const State *s;
    
    while(!p->has_path()){
      pthread_mutex_lock(mut);
      if(!p->open.empty()){
	s = p->open.take();
	pthread_mutex_unlock(mut);
      }
      else{
	cc->complete();
        if (cc->is_complete()){
          p->set_done();
        }
        if (p->done==true){
          pthread_mutex_unlock(mut);
	  if (children)
	    delete children;
          return;
        }
        cc->uncomplete();
	pthread_mutex_unlock(mut);
	continue;
      }

      const State *dup = p->closed.lookup(s);
      if (dup && dup->get_g() < s->get_g()) {
	delete s;
	continue;
      }

      p->closed.add(s);

      if (s->is_goal()) {
        p->set_path(s->get_path());
        break;
      }

      children = p->expand(s);
      for (unsigned int i = 0; i < children->size(); i += 1) {
        const State *c = children->at(i);
        if (p->closed.lookup(c) != NULL) {
          delete c;
          continue;
        }
	pthread_mutex_lock(mut);
        p->open.add(c);
	pthread_mutex_unlock(mut);
      }
    }
    
    delete children;
  }
  
private:
  PAStar *p;
  pthread_mutex_t* mut;
  friend class PAStar;
  CompletionCounter *cc;
};


PAStar::PAStar(unsigned int n_threads) : n_threads(n_threads), path(NULL){
  done = false;
}

void PAStar::set_done()
{
        pthread_mutex_lock(&mutex);
        done = true;
        pthread_mutex_unlock(&mutex);
}

bool PAStar::is_done()
{
        bool ret;
        pthread_mutex_lock(&mutex);
 	ret = done;
        pthread_mutex_unlock(&mutex);
        return ret;
}

void PAStar::set_path(vector<const State *> *path)
{
        pthread_mutex_lock(&mutex);
        if (this->path == NULL){
          this->path = path;
	  done = true;
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
        pthread_mutex_init(&mutex, NULL);

        CompletionCounter cc = CompletionCounter(n_threads);
	pthread_mutex_t m;
        pthread_mutex_init(&m, NULL);

        unsigned int worker;
        vector<PAStarThread *> threads;
	vector<PAStarThread *>::iterator iter;
        for (worker=0; worker<n_threads; worker++) {
		PAStarThread *t = new PAStarThread(this, &m, &cc);
		threads.push_back(t);
		t->start();
        }
	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

 	return path;
}
