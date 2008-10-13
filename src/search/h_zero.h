/* -*- mode:linux -*- */
/**
 * \file h_zero.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-13
 */

#if !defined(_H_ZERO_H_)
#define _H_ZERO_H_

#include "heuristic.h"

class State;

/**
 * An abstract heuristic function.
 */
class HZero : public Heuristic {
public:
	virtual float compute(const State *s) const;
};


#endif	/* !_H_ZERO_H_ */
