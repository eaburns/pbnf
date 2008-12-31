/* -*- mode:linux -*- */
/**
 * \file queue_open_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_QUEUE_OPEN_LIST_H_)
#define _QUEUE_OPEN_LIST_H_

#include <queue>

#include "open_list.h"
#include "state.h"

using namespace std;

class QueueOpenList : public OpenList {
public:
	virtual void add(State *s);
	virtual State *take(void);
	virtual State *peek(void);
	virtual bool empty(void);
	virtual void delete_all_states(void);
private:
	queue<State *> q;
};

#endif	/* !_QUEUE_OPEN_LIST_H_ */
