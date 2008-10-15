/* -*- mode:linux -*- */
/**
 * \file projection.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-15
 */

#if !defined(_PROJECTION_H_)
#define _PROJECTION_H_

#include <vector>

#include "nblock.h"
#include "../state.h"

using namespace std;

/**
 * An abstract projection function class.
 */
class Projection {
public:
	virtual ~Projection();

	virtual NBlock *project(const State *s) = 0;
	virtual vector<NBlock *>get_successors(const NBlock *b) = 0;
	virtual vector<NBlock *>get_predecessors(const NBlock *b) = 0;
};

#endif	/* !_PROJECTION_H_ */
