/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#if !defined(_BFPSDD_NBLOCK_H_)
#define _BFPSDD_NBLOCK_H_

#include <iostream>
#include <set>

#include "../pq_open_list.h"
#include "../closed_list.h"

using namespace std;

namespace BFPSDD {

	template <class StateCompare> struct NBlock {
		NBlock(unsigned int id);

		~NBlock(void);

		void print(ostream &s) const;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<StateCompare> open;

		bool inuse;

		set<NBlock<StateCompare> *> interferes;
		set<NBlock<StateCompare> *> preds;
		set<NBlock<StateCompare> *> succs;
	};

/**
 * Create a new NBlock structure.
 */
	template <class StateCompare>
		NBlock<StateCompare>::NBlock(unsigned int id)
		: id(id),
		sigma(0),
		closed(1000),
		inuse(false) {}



/**
 * Destroy an NBlock and all of its states.
 */
	template <class StateCompare>
		NBlock<StateCompare>::~NBlock(void)
	{
		closed.delete_all_states();
	}


/**
 * Print an NBlock to the given stream.
 */
	template <class StateCompare>
		void NBlock<StateCompare>::print(ostream &o) const
	{
		typename set<NBlock<StateCompare> *>::const_iterator iter;

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

} /* BFPSDD */

#endif	/* !_NBLOCK_H_ */
