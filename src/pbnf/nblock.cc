/**
 * \file nblock.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include <assert.h>

#include <limits>
#include <set>

#include "nblock.h"
#include "../open_list.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

using namespace std;
using namespace PBNF;

/**
 * Create a new NBlock structure.
 */
NBlock::NBlock(unsigned int id)
	: id(id),
	  sigma(0),
	  closed(1000),
	  sigma_hot(0),
	  hot(false),
	  inuse(false) {}


/**
 * Destroy an NBlock and all of its states.
 */
NBlock::~NBlock(void)
{
	closed.delete_all_states();
}

bool NBlock::NBlockCompare::operator()(NBlock *a, NBlock *b)
{
	assert(!a->open.empty());
	assert(!b->open.empty());

	fp_type fa = a->open.peek()->get_f();
	fp_type fb = b->open.peek()->get_f();

	if (fa == fb)
		return a->open.peek()->get_g() < b->open.peek()->get_g();

	return fa > fb;
}


/**
 * Print an NBlock to the given stream.
 */
void NBlock::print(ostream &o)
{
	fp_type best_f;
	set<unsigned int>::const_iterator iter;

	best_f = open.empty() ? fp_infinity : open.peek()->get_f();

	o << "nblock " << id << endl;
	o << "\tsigma: " << sigma << endl;
	o << "\tsigma_hot: " << sigma_hot << endl;
	o << "\thot: " << hot << endl;
	o << "\tinuse: " << inuse << endl;
	o << "\topen: " << (open.empty() ? "false" : "true") << endl;
	o << "\tbest f(n): " << best_f << endl;

	o << "\tinterferes with: ";
	for (iter = interferes.begin(); iter != interferes.end(); iter++)
		o << (*iter) << " ";
	o << endl;

	o << "\tpreds: ";
	for (iter = preds.begin(); iter != preds.end(); iter++)
		o << (*iter) << " ";
	o << endl;

	o << "\tsuccs: ";
	for (iter = succs.begin(); iter != succs.end(); iter++)
		o << (*iter) << " ";
	o << endl;

}
