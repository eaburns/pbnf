/* -*- mode:linux -*- */
/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_NBLOCK_H_)
#define _NBLOCK_H_

#include "../open_list.h"
#include "../closed_list.h"

class NBlock {
public:
	NBlock(OpenList *open, ClosedList *closed, unsigned int hash);

	unsigned int get_hash(void) const;
	OpenList *get_open_list(void);
	ClosedList *get_closed_list(void);

private:
	OpenList *open;
	ClosedList *closed;
	unsigned int hash;
};

#endif	/* !_NBLOCK_H_ */
