/* -*- mode:linux -*- */
/**
 * \file pastar_search.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-11-19
 */

#if !defined(_PRASTAR_H_)
#define _PRASTAR_H_

#include <vector>

#include "state.h"
#include "search.h"
#include "pbnf/nblock_graph.h"
#include "pbnf/nblock.h"
#include "util/thread.h"
#include "synch_pq_olist.h"
#include "synch_closed_list.h"
#include "util/completion_counter.h"

using namespace std;

class PRAStar : public Search {
public:
        PRAStar(unsigned int n_threads);

        virtual ~PRAStar(void);

        virtual vector<const State *> *search(const State *init);
        void set_path(vector<const State *> *path);
        bool has_path();

private:
        class PRAStarThread : public Thread {
        public:
                PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, pthread_cond_t* con, pthread_mutex_t* mut, CompletionCounter* cc);
                virtual ~PRAStarThread(void);
                virtual void run(void);
        private:
		PRAStar *p;
                vector<PRAStarThread *> *threads;
                pthread_cond_t* con;
                pthread_mutex_t* mut;
                CompletionCounter *cc;
                friend class PRAStar;
                SynchPQOList<CompareOnF> open;
                SynchClosedList closed;
                unsigned int id;
        };

        bool done;
        pthread_cond_t cond;
        pthread_mutex_t mutex;
        const unsigned int n_threads;
        vector<const State *> *path;
};

#endif	/* !_PRASTAR_H_ */