/* -*- mode:linux -*- */
/**
 * \file search_domain.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */
#if !defined(_SEARCH_DOMAIN_H_)
#define _SEARCH_DOMAIN_H_

#include <vector>
#include <iostream>

#include "heuristic.h"

using namespace std;

class state;

class SearchDomain {
public:
	SearchDomain();

	virtual void set_heuristic(const Heuristic *h);
	virtual const Heuristic* get_heuristic(void) const;

	/* Abstract methods */
	virtual State *initial_state(void) = 0;
	virtual vector<const State*> *expand(const State *s) const = 0;

private:
	const Heuristic *heuristic;
};

#endif	/* !_SEARCH_DOMAIN_H_ */
