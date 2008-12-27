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

	~KBFSThread() {
          delete children;
	}

	virtual void run(void){
          k->cc.complete();
          wait();
                
          while(!do_exit){
            children = k->expand(s);
            k->cc.complete();
            wait();
          }
        }

private:
	const State *s;
	KBFS *k;
        vector<const State *> *children;
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
        unsigned int worker, i;
        vector<KBFSThread *> threads;
	vector<KBFSThread *>::iterator iter;
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
		    const State *dup = closed.lookup(s);
		    if (dup) {
		      delete s;
		      worker--;
		      continue;
		    }
                    threads[worker]->s = s;
                }

                cc.reset();
                cc.set_max(worker);

                for(i=0; i<worker; i++){
                    threads[i]->signal();
                }
                cc.wait();
		for(i=0; i<worker; i++){
		    for (unsigned int j = 0; 
			 j < threads[i]->children->size(); j += 1) {
		      const State *c = threads[i]->children->at(j);
		      if (closed.lookup(c) != NULL) {
			delete c;
			continue;
		      }
		      closed.add(c);
		      open.add(c);
		    }
		}
 	}

	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

 	closed.delete_all_states();

 	return path;
}
