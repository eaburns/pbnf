/* -*- mode:linux -*- */
/**
 * \file search.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_SEARCH_H_)
#define _SEARCH_H_

class Search {
public:
	virtual vector<const State *> *search(const State *) const = 0;
};

#endif	/* !_SEARCH_H_ */
