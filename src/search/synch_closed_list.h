/* -*- mode:linux -*- */
/**
 * \file synch_closed_list.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-10-13
 */

#if !defined(_SYNCH_CLOSED_LIST_H_)
#define _SYNCH_CLOSED_LIST_H_

#include <pthread.h>

#include "closed_list.h"

/**
 * A thread safe ClosedList implementation.
 */

class SynchClosedList : public ClosedList {
public:
	SynchClosedList(void);

	void add(const State *);
	const State *lookup(const State *);
	void delete_all_states(void);

private:
	pthread_mutex_t mutex;
};

#endif
