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
        void set_done();
        bool is_done();
        void set_path(vector<const State *> *path);
        bool has_path();

private:
        class PRAStarThread : public Thread {
        public:
                PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, CompletionCounter* cc);
                virtual ~PRAStarThread(void);
                virtual void run(void);
                void add(const State* s);
                const State *take(void);

        private:
                PRAStar *p;
                vector<PRAStarThread *> *threads;
		vector<const State *> *q;
                pthread_mutex_t* mut;
                pthread_mutex_t mutex;
                bool completed;
                CompletionCounter *cc;
                friend class PRAStar;
                PQOpenList<CompareOnF> open;
                ClosedList closed;
        };

        bool done;
        pthread_cond_t cond;
        pthread_mutex_t mutex;
        const unsigned int n_threads;
        vector<const State *> *path;
};

#endif	/* !_PRASTAR_H_ */
