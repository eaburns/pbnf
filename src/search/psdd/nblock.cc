/* -*- mode:linux -*- */
/**
 * \file nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include <assert.h>

#include <vector>

#include "nblock.h"
#include "../open_list.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

using namespace std;
using namespace PSDD;

/**
 * Create a new NBlock structure.
 */
NBlock::NBlock(unsigned int id)
	: id(id),
	  sigma(0),
	  cur_open(&open_a),
	  next_open(&open_b) {}



/**
 * Destroy an NBlock and all of its states.
 */
NBlock::~NBlock(void)
{
	open_a.delete_all_states();
	open_b.delete_all_states();
	closed.delete_all_states();
}

/**
 * Swap the current and next open lists in this NBlock.
 */
void NBlock::next_iteration(void)
{
	OpenList *tmp;

	assert(cur_open->empty());
	assert(sigma == 0);

	tmp = cur_open;
	cur_open = next_open;
	next_open = tmp;
}

/**
 * Print an NBlock to the given stream.
 */
void NBlock::print(ostream &o) const
{
	set<NBlock *>::const_iterator iter;

	o << "nblock " << id << endl;
	o << "\tsigma: " << sigma << endl;

	o << "\tinterferes with: ";
	for (iter = interferes.begin(); iter != interferes.end(); iter++)
		o << (*iter)->id << " ";
	o << endl;

	o << "\tpreds: ";
	for (iter = preds.begin(); iter != preds.end(); iter++)
		o << (*iter)->id << " ";
	o << endl;

	o << "\tsuccs: ";
	for (iter = succs.begin(); iter != succs.end(); iter++)
		o << (*iter)->id << " ";
	o << endl;

}
