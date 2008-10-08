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
	SearchDomain(const Heuristic *h);

	virtual float h_val(const State *) const;

	/* Abstract methods */
	virtual State *initial_state(void) = 0;
	virtual vector<const State*> *expand(const State *s) const = 0;

private:
	const Heuristic *h;
};

#endif	/* !_SEARCH_DOMAIN_H_ */
