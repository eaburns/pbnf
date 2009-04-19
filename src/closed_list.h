/**
 * \file closed_list.h
 *
 * A simple closed list class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_CLOSED_LIST_H_)
#define _CLOSED_LIST_H_

#include "util/hash_table.h"
#include "state.h"

using namespace std;

/**
 * A simple closed list class.
 */
class ClosedList {
public:
	ClosedList(void);
	ClosedList(unsigned long size);
	virtual ~ClosedList(void);
	virtual void add(State *);
	virtual State *lookup(State *);
	virtual void delete_all_states(void);
	virtual bool empty();

	virtual void prune(void);

private:
	HashTable<State> tbl;
};

#endif	/* !_CLOSED_LIST_H_ */
