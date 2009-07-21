/**
 * \file prastar.h
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
#include "util/mutex.h"
#include "util/msg_buffer.h"
#include "util/atomic_int.h"
#include "util/thread.h"
#include "synch_pq_olist.h"
#include "synch_closed_list.h"
#include "util/completion_counter.h"


using namespace std;

class PRAStar : public Search {
public:
        PRAStar(unsigned int n_threads, bool use_abst);

        virtual ~PRAStar(void);

        virtual vector<State *> *search(Timer *t, State *init);
        void set_done();
        bool is_done();
        void set_path(vector<State *> *path);
        bool has_path();

	virtual void output_stats(void);

private:
        class PRAStarThread : public Thread {
        public:
                PRAStarThread(PRAStar *p, vector<PRAStarThread *> *threads, CompletionCounter* cc);
                virtual ~PRAStarThread(void);
                virtual void run(void);

		/**
		 * Gets a pointer to the message queue.
		 */
	        vector<State*> *get_queue(void);

		/**
		 * Gets the lock on the message queue.
		 */
		Mutex *get_mutex(void);

		/**
		 * Should be called when the message queue has had
		 * things added to it.
		 */
		static void post_send(void *thr);

                State *take(void);

        private:
		/* Flushes the send queues. */
		void flush_sends(bool force);


		/* flushes the queue into the open list. */
                void flush_receives(void);

		/* sends the state to the appropriate thread (possibly
		 * this thread). */
		void send_state(State *c, bool force);

                PRAStar *p;

		/* List of the other threads */
                vector<PRAStarThread *> *threads;

		/* The incoming message queue. */
		vector<State *> q;
		Mutex mutex;

		/* The outgoing message queues (allocated lazily). */
		vector<MsgBuffer<State*>* > out_qs;

		/* Marks whether or not this thread has posted completion */
                bool completed;

		/* A pointer to the completion counter. */
                CompletionCounter *cc;

                friend class PRAStar;

		/* Search queues */
                PQOpenList<State::PQOpsFPrime> open;
                ClosedList closed;
		bool q_empty;
        };

        bool done;
        pthread_cond_t cond;
        Mutex mutex;
        const unsigned int n_threads;
	AtomicInt bound;
	const Projection *project;
        vector<State *> *path;
	vector<PRAStarThread *> threads;
	vector<PRAStarThread *>::iterator iter;

	/* true: use abstraction for hashing, false: use basic
	 * hashing. */
	bool use_abstraction;

	double lock_acquisition_time;
};

#endif	/* !_PRASTAR_H_ */
