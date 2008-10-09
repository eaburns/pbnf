/* -*- mode:linux -*- */
/**
 * \file heuristic.h
 *
 * A heuristic function.
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#if !defined(_HEURISTIC_H_)
#define _HEURISTIC_H_

class State;

/**
 * An abstract heuristic function.
 */
class Heuristic {
public:
	virtual float compute(const State *s) const = 0;
};

#endif	/* !_HEURISTIC_H_ */
