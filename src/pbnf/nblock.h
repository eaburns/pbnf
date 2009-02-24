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
			bool operator()(NBlock *a, NBlock *b)
			{
				assert(!a->open.empty());
				assert(!b->open.empty());
				fp_type fpa = a->open.peek()->get_f_prime();
				fp_type fpb = b->open.peek()->get_f_prime();
				if (fpa == fpb) {
					fp_type fa = a->open.peek()->get_f();
					fp_type fb = b->open.peek()->get_f();
					if (fa == fb)
						return a->open.peek()->get_g() < b->open.peek()->get_g();
					else
						return fa > fb;
				}
				return fpa > fpb;
			}
		};

		static NBlockCompare compare;

		unsigned int id;
		unsigned int sigma;
		ClosedList closed;
		PQOpenList<State::PQOpsFPrime> open;

		unsigned int sigma_hot;
		int hot;
		int inuse;

		set<unsigned int> interferes;
		set<unsigned int> preds;
		set<unsigned int> succs;
	};
}	/* PBNF */
#endif	/* !_NBLOCK_H_ */
