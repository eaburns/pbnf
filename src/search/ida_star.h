/* -*- mode:linux -*- */
/**
 * \file ida_star.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#if !defined(_IDA_STAR_H_)
#define _IDA_STAR_H_

#include <vector>

#include "state.h"
#include "search.h"

using namespace std;

class IDAStar : public Search {
public:
	virtual vector<const State *> *search(const State *);
};

#endif	/* !_IDA_STAR_H_ */
