/* -*- mode:linux -*- */
/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#if !defined(_NBLOCK_H_)
#define _NBLOCK_H_

#include <iostream>
#include <vector>

#include "../open_list.h"
#include "../pq_open_list.h"
#include "../closed_list.h"

using namespace std;

namespace PBNF {
/**
 * An NBlock
 */
	struct NBlock {
		NBlock(unsigned int id,
		       vector<unsigned int> preds,
		       vector<unsigned int> succs);

		~NBlock(void);

		void next_iteration(void);
		bool operator<(NBlock *a);
		void print(ostream &s) const;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList open;
		vector<unsigned int> preds;
		vector<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
