/* -*- mode:linux -*- */
/**
 * \file pastar.h
 *
 * Contains the PAStar class.
 *
 * \author Seth Lemons
 * \date 2008-11-02
 */

#if !defined(_PASTAR_H_)
#define _PASTAR_H_

#include "state.h"
#include "search.h"
#include "synch_pq_olist.h"
#include "synch_closed_list.h"
#include "util/completion_counter.h"

/**
 * A Parallel A* search class.
 */
class PAStar : public Search {
public:
	PAStar(unsigned int);
	virtual vector<const State *> *search(const State *);
        void set_path(vector<const State *> *path);
        bool has_path();
private:
	SynchPQOList open;
	SynchClosedList closed;
	pthread_cond_t cond;
        bool done;
	pthread_mutex_t mutex;
        friend class PAStarThread;
        const unsigned int n_threads;
        vector<const State *> *path;
};

#endif	/* !_PASTAR_H_ */
