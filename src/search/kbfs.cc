/* -*- mode:linux -*- */
/**
 * \file kbfs.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-10-09
 */

#include <pthread.h>
#include "state.h"
#include "open_list.h"
#include "closed_list.h"
#include "kbfs.h"

#define NTHREADS 2

/**
 * Perform a KBFS search.
 */


vector<const State *> *KBFS::search(const State *init)
{
	vector<const State *> *path = NULL;
	OpenList open;
	ClosedList closed;
        pthread_t threads[NTHREADS];
        vector<const State *> *children;
        int worker;

	open.push(init);
	closed.add(init);

	while (!open.empty() && !path) {
                const State *s;
                for (worker=0; worker<NTHREADS; worker++) {
                    s = open.pop();
                    pthread_create(&threads[worker], NULL, expand, s);
                }
                for (worker=0; worker<NTHREADS; worker++) {
                    pthread_join(threads[worker],(void *) &children);

                    for (unsigned int i = 0; i < children->size(); i += 1) {
                            const State *c = children->at(i);
                            if (c->is_goal()) {
                                    path = c->get_path();
                                    for (; i < children->size(); i += 1)
                                            delete children->at(i);
                                    break;
                            }
                            if (closed.lookup(c) != NULL) {
                                    delete c;
                                    continue;
                            }
                            closed.add(c);
                            open.push(c);
                    }
                }
		delete children;
	}

	closed.delete_all_states();

	return path;
}
