/* -*- mode:linux -*- */
/**
 * \file idpsdd_search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-12-22
 */

#if !defined(_IDPSDD_SEARCH_H_)
#define _IDPSDD_SEARCH_H_

#include "search.h"
#include "state.h"

class IDPSDDSearch : public Search {
public:
	IDPSDDSearch(unsigned int n_threads);

	virtual vector<State *> *search(State *s);

private:
	unsigned int n_threads;
};

#endif	/* !_IDPSDD_SEARCH_H_ */
