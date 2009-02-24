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
void OpenList::set_best_val(fp_type f)
{
	best.set(f);
}

fp_type OpenList::get_best_val(void)
{
	return best.read();
}
