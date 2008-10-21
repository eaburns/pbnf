/* -*- mode:linux -*- */
/**
 * \file nblock_free_list.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_NBLOCK_FREE_LIST_H_)
#define _NBLOCK_FREE_LIST_H_

#include "nblock.h"

class NBlockFreeList {
public:
	virtual ~NBlockFreeList(void);

	/* get the next free nblock (doesn't remove it from the list). */
	virtual NBlock *next(void) = 0;
	virtual void remove(NBlock *b) = 0;
	virtual void add(NBlock *b) = 0;
};

#endif	/* !_NBLOCK_FREE_LIST_H_ */
