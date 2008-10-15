/* -*- mode:linux -*- */
/**
 * \file nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-15
 */

#include "nblock.h"

/** Create a new NBlock. */
NBlock::NBlock(unsigned int hash)
	: hash(hash), sigma(0) {}

/**
 * Get the hash value of this NBlock
 * \return The unique hash value of this nblock.  This should match
 *         the projection value of states belonging to this block.
 */
unsigned int NBlock::get_hash(void) const
{
	return hash;
}

float NBlock::get_best_f(void) const
{
	// not implemented yet
	return -1.0;
}

/**
 * Get the closed list for this nblock.
 * \return the ClosedList for this nblock.
 */
ClosedList *NBlock::get_closed_list(void)
{
	return &closed;
}

/**
 * Get the open list for this nblock.
 * \return the OpenList for this nblock.
 */
OpenList *NBlock::get_open_list(void)
{
	return &open;
}

/**
 * Get the sigma value for this nblock.  Sigma is the number of
 * predecessors which are in use by a precessor.
 * \return Sigma.
 */
unsigned int NBlock::get_sigma(void) const
{
	return sigma;
}

/**
 * Increment the sigma value of this nblock.
 */
void NBlock::inc_sigma(void)
{
	sigma += 1;
}

/**
 * Decrement the sigma value of this nblock.
 */
void NBlock::dec_sigma(void)
{
	sigma -= 1;
}
