/* -*- mode:linux -*- */
/**
 * \file nblock.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-15
 */

#if !defined(_NBLOCK_H_)
#define _NBLOCK_H_

#include "../closed_list.h"
#include "../pq_open_list.h"

class NBlock {
public:
	NBlock(unsigned int hash);

	unsigned int get_hash(void) const;
	float get_best_f(void) const;
	ClosedList *get_closed_list(void);
	OpenList *get_open_list(void);
	unsigned int get_sigma(void) const;
	void inc_sigma(void);
	void dec_sigma(void);
private:
	unsigned int hash;
	unsigned int sigma;
	ClosedList closed;
	PQOpenList open;
};

#endif	/* !_NBLOCK_H_ */
