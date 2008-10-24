/* -*- mode:linux -*- */
/**
 * \file a_star.h
 *
 * Contains the AStar class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_A_STAR_H_)
#define _A_STAR_H_

#include "state.h"
#include "search.h"

/**
 * An A* search class.
 */
class AStar : public Search {
public:
	virtual ~AStar(void);
	virtual vector<const State *> *search(const State *);
};

#endif	/* !_A_STAR_H_ */
