/* -*- mode:linux -*- */
/**
 * \file kbfs.h
 *
 * Contains the KBFS class.
 *
 * \author Seth Lemons
 * \date 2008-10-09
 */

#if !defined(_KBFS_H_)
#define _KBFS_H_

#include "state.h"
#include "search.h"

/**
 * A KBFS search class.
 */
class KBFS : public Search {
public:
	virtual vector<const State *> *search(const State *);
};

#endif	/* !_KBFS_H_ */
