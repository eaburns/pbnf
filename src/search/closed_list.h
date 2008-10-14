/* -*- mode:linux -*- */
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

#include <map>

#include "state.h"

using namespace std;

/**
 * A simple closed list class.  This class is just a wrapper for the
 * C++ STL map class for states.
 */
class ClosedList {
public:
	void add(const State *);
	const State *lookup(const State *);
	void delete_all_states(void);

private:
	map<int, const State *> m;
};

#endif	/* !_CLOSED_LIST_H_ */
