/* -*- mode:linux -*- */
/**
 * \file nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include "nblock.h"
#include "../open_list.h"
#include "../closed_list.h"

NBlock::NBlock(OpenList *open, ClosedList *closed, unsigned int hash)
	: open(open), closed(closed), hash(hash) {}

/**
 * Get the hash value.
 */
unsigned int NBlock::get_hash(void) const
{
	return hash;
}


/**
 * Get the OpenList for this NBlock.
 */
OpenList *NBlock::get_open_list(void)
{
	return open;
}

/**
 * Get the ClosedList for the NBlock.
 */
ClosedList *NBlock::get_closed_list(void)
{
	return closed;
}
