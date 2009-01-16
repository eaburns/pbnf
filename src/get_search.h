/**
 * \file get_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-13
 */

#if !defined(_GET_SEARCH_H_)
#define _GET_SEARCH_H_

#include "util/fixed_point.h"

class Search;

extern unsigned int threads;
extern fp_type cost_bound;
extern unsigned int nblocks;
extern fp_type weight;

Search *get_search(int argc, char *argv[]);

#endif	/* !_GET_SEARCH_H_ */
