/* -*- mode:linux -*- */
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

class Search;

extern unsigned int threads;
extern float cost_bound;
extern float ratio;
extern float weight;

Search *get_search(int argc, char *argv[]);

#endif	/* !_GET_SEARCH_H_ */
