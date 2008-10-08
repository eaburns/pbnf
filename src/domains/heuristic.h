/* -*- mode:linux -*- */
/**
 * \file heuristic.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#if !defined(_HEURISTIC_H_)
#define _HEURISTIC_H_

class State;

class Heuristic {
public:
	virtual float compute(const State *s) const;
};

#endif	/* !_HEURISTIC_H_ */
