/**
 * \file lf_closedlist.h
 *
 *
 *
 * \author eaburns
 * \date 2009-04-12
 */

#if !defined(_LF_CLOSEDLIST_H_)
#define _LF_CLOSEDLIST_H_

#include "state.h"
#include "closed_list.h"

using namespace std;

extern "C" {
#include "lockfree/include/lockfree.h"
}

/**
 * A simple closed list class.
 */
class LF_ClosedList : public ClosedList {
public:
	LF_ClosedList(void);
	~LF_ClosedList(void);

	void add(State *);

	/**
	 * Conditionally update the closed list if the new state is
	 * still better than the previous state.
	 */
	State *cond_update(State *);

	State *lookup(State *);
	void delete_all_states(void);

private:

	static int better(void *, void *);

	struct lf_hashtbl *tbl;
};

#endif	/* !_LF_CLOSEDLIST_H_ */
