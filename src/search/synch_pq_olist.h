/* -*- mode:linux -*- */
/**
 * \file safe_pq_olist.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_SYNCH_PQ_OLIST_H_)
#define _SYNCH_PQ_OLIST_H_

#include <pthread.h>

#include "pq_open_list.h"

/**
 * A thread safe PQ OpenList implementation.
 */
class SynchPQOList : public PQOpenList {
public:
	SynchPQOList(void);

	virtual void add(const State *s);
	virtual const State *take(void);
	virtual bool empty(void);
	virtual void delete_all_states(void);
private:
	pthread_mutex_t mutex;
};

#endif	/* !_SYNCH_PQ_OLIST_H_ */
