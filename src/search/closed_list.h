/* -*- mode:linux -*- */
/**
 * \file closed_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_CLOSED_LIST_H_)
#define _CLOSED_LIST_H_

#include <map>

#include "state.h"

using namespace std;

class ClosedList {
public:
	void add(const State *);
	const State *lookup(const State *) const;
	void delete_all_states(void);

private:
	map<int, const State *> m;
};

#endif	/* !_CLOSED_LIST_H_ */
