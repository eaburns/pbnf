/* -*- mode:linux -*- */
/**
 * \file stack_open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#include <stack>

#include "stack_open_list.h"

using namespace std;

void StackOpenList::add(const State *s)
{
	stack.push(s);
}

const State *StackOpenList::take(void)
{
	const State *ret;

	ret = stack.top();
	stack.pop();

	return ret;
}

bool StackOpenList::empty(void)
{
	return stack.empty();
}
