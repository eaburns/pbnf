/* -*- mode:linux -*- */
/**
 * \file breadth_first_nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_BREADTH_FIRST_NBLOCK_H_)
#define _BREADTH_FIRST_NBLOCK_H_

#include "nblock.h"
#include "nblock_factory.h"

class BreadthFirstNBlockFactory : NBlockFactory {
public:
	virtual ~BreadthFirstNBlockFactory();
	virtual NBlock *new_nblock(unsigned int hash) const;
};

class BreadthFirstNBlock : public NBlock {
public:
	BreadthFirstNBlock(unsigned int hash);
};

#endif	/* !_BREADTH_FIRST_NBLOCK_H_ */
