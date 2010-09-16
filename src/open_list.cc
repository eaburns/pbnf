/**
 * \file open_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-13
 */

#include "open_list.h"

#if defined(COUNT_FS)
F_hist OpenList::fs;
#endif // COUNT_FS

OpenList::OpenList()
{
	best.set(fp_infinity);
	cur_size = 0;
	max_size = 0;
}

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

unsigned int OpenList::size()
{
	return cur_size;
}

void OpenList::set_size(unsigned int s)
{
#if defined(INSTRUMENTED)
	cur_size = s;
	if (s > max_size)
		max_size = s;
	avg_size.add_val(s);
#endif	// INSTRUMENTED
}

void OpenList::change_size(unsigned int delta)
{
#if defined(INSTRUMENTED)
	cur_size += delta;
	if (cur_size > max_size)
		max_size = cur_size;
	avg_size.add_val(cur_size);
#endif	// INSTRUMENTED
}

#if defined(INSTRUMENTED)
void OpenList::print_stats(ostream &o)
{
	o << "average-open-size: " << avg_size.read() << endl;
	o << "max-open-size: " << max_size << endl;
}

float OpenList::get_avg_size()
{
	return avg_size.read();
}

unsigned int OpenList::get_max_size()
{
	return max_size;
}

#else  // INSTRUMENTED
void OpenList::print_stats(ostream &o)
{
}
#endif	// INSTRUMENTED


#if defined(COUNT_FS)
F_hist &OpenList::get_fs(void)
{
	return fs;
}
#endif // COUNT_FS
