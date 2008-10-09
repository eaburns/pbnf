/* -*- mode:linux -*- */
/**
 * \file manhattan_dist.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */

#if !defined(_MANHATTAN_DIST_H_)
#define _MANHATTAN_DIST_H_

#include "grid_world.h"
#include "../heuristic.h"

class ManhattanDist : public Heuristic {
public:
	ManhattanDist(int goal_x, int goal_y);
	virtual float compute(const State *s) const;
private:
	int goal_x, goal_y;
};

#endif /* !_MANHATTAN_DIST_H_ */
