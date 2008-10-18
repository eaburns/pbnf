/* -*- mode:linux -*- */
/**
 * \file kbfs.cc
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-10-09
 */

#include "state.h"
#include "kbfs.h"

#define NTHREADS 2

struct input_struct{
	const State *s;
	KBFS *k;
};

void *thread_expand(void *inf)
{
        input_struct *info = (input_struct *)inf;
        const State *s = info->s;
        KBFS *k = info->k;
        SynchPQOList open = info->k->open;
	SynchClosedList closed = info->k->closed;
//        vector<const State *> *children = k->expand(s);

        printf("test\n");
        fflush(stdout);
//         for (unsigned int i = 0; i < children->size(); i += 1) {
//           const State *c = children->at(i);
//           if (closed.lookup(c) != NULL) {
//             delete c;
//             continue;
//           }
//           closed.add(c);
//           open.add(c);
//         }
//         delete children;
        return NULL;
}


/**
 * Perform a KBFS search.
 */
vector<const State *> *KBFS::search(const State *init)
{
 	vector<const State *> *path = NULL;
        int worker;
        pthread_t threads[NTHREADS];
        printf("starting search\n");
        fflush(stdout);

 	open.add(init);
 	closed.add(init);
        

 	while (!open.empty() && !path) {
                for (worker=0; worker<NTHREADS & !open.empty(); worker++) {
                    const State *s = open.take();
                    if (s->is_goal()) {
                      path = s->get_path();
                      break;
                    }
                    input_struct *info;
                    info->k = this;
                    info->s = s;
                    printf("creating %i\n", worker);
                    fflush(stdout);
                    //pthread_create(&threads[worker], NULL, thread_expand, (void *) &info);
                    printf("created %i\n", worker);
                    fflush(stdout);
                }
                int i;
                for (i=0; i<worker; i++) {
                    printf("joining %i\n", i);
                    fflush(stdout);
                    //pthread_join(threads[worker], NULL);
                    printf("joined %i\n", i);
                    fflush(stdout);
                }
 	}
        
        printf("finishing search\n");

 	closed.delete_all_states();

 	return path;
}
