/* -*- mode:linux -*- */
/**
 * \file open_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_OPEN_LIST_H_)
#define _OPEN_LIST_H_

#include "util/atomic_float.h"

#include "state.h"

/**
 * Defines the interface to an OpenList.
 */
class OpenList {
public:
	virtual ~OpenList();

	virtual void add(const State *s) = 0;
	virtual const State *take(void) = 0;
	virtual const State *peek(void) = 0;
	virtual bool empty(void) = 0;
	virtual void delete_all_states(void) = 0;

	double get_best_f(void);
protected:
	void set_best_f(double f);
private:
	AtomicFloat best;
};

#endif	/* !_OPEN_LIST_H_ */
