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
#include <set>

#include "../open_list.h"
#include "../queue_open_list.h"
#include "../closed_list.h"

using namespace std;

namespace PSDD {

/**
 * An NBlock
 */
	struct NBlock {
		NBlock(unsigned int id);

		~NBlock(void);

		void print(ostream &s) const;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		QueueOpenList open[2];

		bool inuse;

		set<NBlock *> interferes;
		set<NBlock *> preds;
		set<NBlock *> succs;
	};

} /* PSDD */

#endif	/* !_NBLOCK_H_ */
