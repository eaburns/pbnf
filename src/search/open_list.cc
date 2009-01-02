/**
 * \file open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-13
 */

#include "open_list.h"

OpenList::~OpenList() {}

/**
 * Track the best open state.
 */
void OpenList::set_best_f(double f)
{
	best.set(f);
}

double OpenList::get_best_f(void)
{
	return best.read();
}
