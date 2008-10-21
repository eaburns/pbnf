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

#define NTHREADS 2

class KBFSThread : public Thread {
public:
	KBFSThread(){}
	KBFSThread(KBFS *k) : k(k) {}
	KBFSThread(const State *s, KBFS *k) : s(s), k(k) {}

	~KBFSThread() {}

	virtual void run(void){
                vector<const State *> *children = k->expand(s);

                for (unsigned int i = 0; i < children->size(); i += 1) {
                        const State *c = children->at(i);
                        if (k->closed.lookup(c) != NULL) {
                        	delete c;
                                continue;
                        }
                  k->closed.add(c);
                  k->open.add(c);
                }
                delete children;
        }

private:
	const State *s;
	KBFS *k;
        friend class KBFS;
};


/**
 * Perform a KBFS search.
 */
vector<const State *> *KBFS::search(const State *init)
{
 	vector<const State *> *path = NULL;
        int worker;
        KBFSThread threads[NTHREADS];
        for (worker=0; worker<NTHREADS; worker++) {
          threads[worker] = KBFSThread(this);
        }

 	open.add(init);
 	closed.add(init);
        

 	while (!open.empty() && !path) {
                for (worker=0; worker<NTHREADS & !open.empty(); worker++) {
                    const State *s = open.take();
                    if (s->is_goal()) {
                      path = s->get_path();
                      break;
                    }
                    threads[worker].s = s;
                    threads[worker].start();
                }
                int i;
                for (i=0; i<worker; i++) {
                    threads[i].join();
                }
 	}

 	closed.delete_all_states();

 	return path;
}
