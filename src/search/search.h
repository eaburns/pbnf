/* -*- mode:linux -*- */
/**
 * \file search.h
 *
 * Abstract search classe
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_SEARCH_H_)
#define _SEARCH_H_

#include <vector>

#include "state.h"

using namespace std;

/**
 * An abstract search class that collects some statistics.
 */
class Search {
public:
	Search(void);
	virtual ~Search() {}

	virtual vector<const State *> *search(const State *) = 0;

	void clear_counts(void);
	unsigned long get_expanded(void) const;
	unsigned long get_generated(void) const;

protected:
	vector<const State *> *expand(const State *);

	void set_expanded(unsigned long e);
	void set_generated(unsigned long g);

private:
	unsigned long expanded;
	unsigned long generated;
};

#endif	/* !_SEARCH_H_ */
