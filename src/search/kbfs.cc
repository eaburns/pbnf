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
        printf("starting expand\n");
        fflush(stdout);
        input_struct *info = new input_struct;
        info = (input_struct *)inf;
        vector<const State *> *children = info->k->expand(info->s);

        printf("test\n");
        fflush(stdout);
        for (unsigned int i = 0; i < children->size(); i += 1) {
          printf("child %i\n", i);
          fflush(stdout);
          const State *c = children->at(i);
          if (info->k->closed.lookup(c) != NULL) {
            delete c;
            continue;
          }
          info->k->closed.add(c);
          info->k->open.add(c);
        }
        delete children;
        printf("finishing expand\n");
        fflush(stdout);
        return NULL;
}

vector<const State *> *KBFS::expand(const State *s)
{
  pthread_mutex_lock(&mutex);
  vector<const State *> *children = Search::expand(s);
  pthread_mutex_unlock(&mutex);
  return children;
}


/**
 * Perform a KBFS search.
 */
vector<const State *> *KBFS::search(const State *init)
{
        pthread_mutex_init(&mutex, NULL);
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
                    input_struct *info = new input_struct;
                    info->k = this;
                    info->s = s;
                    printf("creating %i\n", worker);
                    fflush(stdout);
                    pthread_create(&threads[worker], NULL, thread_expand, (void *) &info);
                    printf("created %i\n", worker);
                    fflush(stdout);
                    delete info;
                }
                int i;
                for (i=0; i<worker; i++) {
                    printf("joining %i\n", i);
                    fflush(stdout);
                    pthread_join(threads[worker], NULL);
                    printf("joined %i\n", i);
                    fflush(stdout);
                }
                sleep(10);
 	}
        
        printf("finishing search\n");

 	closed.delete_all_states();

 	return path;
}
