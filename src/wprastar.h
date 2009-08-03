/**
 * \file wprastar.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2009-03-19
 */

#if !defined(_WPRASTAR_H_)
#define _WPRASTAR_H_

#include <vector>

#include "state.h"
#include "search.h"
#include "pbnf/nblock_graph.h"
#include "pbnf/nblock.h"
#include "util/atomic_int.h"
#include "util/thread.h"
#include "synch_pq_olist.h"
#include "synch_closed_list.h"
#include "util/completion_counter.h"

using namespace std;

class wPRAStar : public Search {
public:
        wPRAStar(unsigned int n_threads, bool dd, bool abst);
        wPRAStar(unsigned int n_threads, fp_type bound, bool dd, bool abst);

        virtual ~wPRAStar(void);

        virtual vector<State *> *search(Timer *t, State *init);
        void set_done();
        bool is_done();
        void set_path(vector<State *> *path);

	void set_bound(fp_type bound);

private:
        class wPRAStarThread : public Thread {
        public:
                wPRAStarThread(wPRAStar *p, vector<wPRAStarThread *> *threads, CompletionCounter* cc);
                virtual ~wPRAStarThread(void);
                virtual void run(void);
                void add(State* s, bool self_add);
                State *take(void);


        private:
                void flush_queue(void);
                wPRAStar *p;
                vector<wPRAStarThread *> *threads;
		vector<State *> q;
		Mutex mutex;
                bool completed;
                CompletionCounter *cc;
                friend class wPRAStar;
                PQOpenList<State::PQOpsFPrime> open;
                ClosedList closed;
		bool q_empty;
        };

        const unsigned int n_threads;
	fp_type weight;
	AtomicInt bound;
        bool done;
	Mutex mutex;
	const Projection *project;
	vector<wPRAStarThread *> threads;
	vector<wPRAStarThread *>::iterator iter;

	SolutionStream *solutions;

	bool dd;		/* Use duplicate detection? */
	bool use_abstraction;	/* Use abstraction for hashing? */
};

#endif	/* !_WPRASTAR_H_ */
