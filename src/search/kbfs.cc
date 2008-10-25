/* -*- mode:linux -*- */
/**
 * \file kbfs.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-10-09
 */

#include "util/thread.h"
#include "state.h"
#include "kbfs.h"

class KBFSThread : public Thread {
public:
	KBFSThread(){}
	KBFSThread(KBFS *k) : k(k) {}
	KBFSThread(const State *s, KBFS *k) : s(s), k(k) {}

	~KBFSThread() {}

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
	KBFS *k;
        friend class KBFS;
};

KBFS::KBFS(unsigned int n_threads)
	: n_threads(n_threads)
{
	cc = CompletionCounter(n_threads);
}


/**
 * Perform a KBFS search.
 */
vector<const State *> *KBFS::search(const State *init)
{
 	vector<const State *> *path = NULL;
        unsigned int worker;
        vector<KBFSThread *> threads;
        for (worker=0; worker<n_threads; worker++) {
        	KBFSThread *t = new KBFSThread(this);
		threads.push_back(t);
		t->start();
        }
        cc.wait();

 	open.add(init);
 	closed.add(init);

 	while (!open.empty() && !path) {
         	for (worker=0; (worker<n_threads) && !open.empty(); worker++) {
                    const State *s = open.take();
                    if (s->is_goal()) {
                      path = s->get_path();
                      break;
                    }
                    threads[worker]->s = s;
                }

                cc.set_max(worker);
                cc.reset();

                for(unsigned int i=0; i<worker; i++){
                    threads[i]->signal();
                }

                cc.wait();
 	}
        for (worker=0; worker<n_threads; worker++) {
          threads[worker]->join();
        }

 	closed.delete_all_states();

 	return path;
}
