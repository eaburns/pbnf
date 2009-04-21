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
	QueueOpenList(void);
	void add(State *s);
	State *take(void);
	State *peek(void);
	bool empty(void);
	void delete_all_states(void);
	void prune(void);
	unsigned int size(void);
private:
	queue<State *> q;
};

#endif	/* !_QUEUE_OPEN_LIST_H_ */
