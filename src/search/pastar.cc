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
	PAStarThread(){}
	PAStarThread(PAStar *k) : k(k) {}
	PAStarThread(const State *s, PAStar *k) : s(s), k(k) {}

	~PAStarThread() {}

	virtual void run(void){
          k->cc.complete();
          wait();
          vector<const State *> *children;
                
          while(!exit){
            children = k->expand(s);
            for (unsigned int i = 0; i < children->size(); i += 1) {
              const State *c = children->at(i);
              if (k->closed.lookup(c) != NULL) {
                delete c;
                continue;
              }
              k->closed.add(c);
              k->open.add(c);
            }
            k->cc.complete();
            wait();
          }
          delete children;
        }

private:
	const State *s;
	PAStar *k;
        friend class PAStar;
};


PAStar::PAStar(unsigned int n_threads)
	: n_threads(n_threads)
{
	cc = CompletionCounter(n_threads);
}


/**
 * Perform a Parallel A* search.
 */
vector<const State *> *PAStar::search(const State *init)
{
 	vector<const State *> *path = NULL;
        unsigned int worker;
        vector<PAStarThread *> threads;
	vector<PAStarThread *>::iterator iter;
        for (worker=0; worker<n_threads; worker++) {
        	PAStarThread *t = new PAStarThread(this);
		threads.push_back(t);
		t->start();
        }
        cc.wait();

 	open.add(init);
 	closed.add(init);


 	while (!open.empty() && !path) {
                cc.reset();

         	for (worker=0; (worker<n_threads) && !open.empty(); worker++) {
                    const State *s = open.take();
                    if (s->is_goal()) {
                      path = s->get_path();
                      break;
                    }
                    threads[worker]->s = s;
                    threads[worker]->signal();
                }

                cc.set_max(worker);
                cc.wait();
 	}
	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

 	closed.delete_all_states();

 	return path;
}
