/* -*- mode:linux -*- */
/**
 * \file breadth_first_nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#include "nblock.h"
#include "breadth_first_nblock.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

NBlock *BreadthFirstNBlockFactory::new_nblock(unsigned int hash) const
{
	return new BreadthFirstNBlock(hash);
}


BreadthFirstNBlockFactory::~BreadthFirstNBlockFactory() {}


BreadthFirstNBlock::BreadthFirstNBlock(unsigned int hash)
	: NBlock(new QueueOpenList(), new ClosedList(), hash) {}
