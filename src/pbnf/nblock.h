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

#include <pthread.h>
#include <iostream>
#include <set>

#include "../open_list.h"
#include "../pq_open_list.h"
#include "../closed_list.h"
#include "../projection.h"

using namespace std;

namespace PBNF {
/**
 * An NBlock
 */
	struct NBlock {
		NBlock(const Projection *p, unsigned int id);

		~NBlock(void);

		void next_iteration(void);
		bool operator<(NBlock *a);
		void print(ostream &s);

		class NBlockCompare {
		public:
			bool operator()(NBlock *a, NBlock *b);
		};

		static NBlockCompare compare;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<State::CompareOnFPrime> open;

		unsigned int sigma_hot;
		int hot;
		int inuse;

		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
