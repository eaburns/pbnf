/* -*- mode:linux -*- */
/**
 * \file stack_open_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_STACK_OPEN_LIST_H_)
#define _STACK_OPEN_LIST_H_

#include <stack>

#include "open_list.h"

using namespace std;

/**
 * An openlist implemented with a stack.
 */
class StackOpenList : public OpenList {
public:
	virtual void add(const State *s);
	virtual const State *take(void);
	virtual bool empty(void);
private:
	stack<const State *> stack;
};

#endif	/* !_STACK_OPEN_LIST_H_ */
