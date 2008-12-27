/* -*- mode:linux -*- */
/**
 * \file kbfs.h
 *
 * Contains the KBFS class.
 *
 * \author Seth Lemons
 * \date 2008-10-09
 */

#if !defined(_KBFS_H_)
#define _KBFS_H_

#include "state.h"
#include "search.h"
#include "pq_open_list.h"
#include "synch_pq_olist.h"
#include "synch_closed_list.h"
#include "util/completion_counter.h"

/**
 * A KBFS search class.
 */
class KBFS : public Search {
public:
	KBFS(unsigned int);
	virtual vector<const State *> *search(const State *);
private:
	PQOpenList<CompareOnF> open;
	ClosedList closed;
        friend class KBFSThread;
        CompletionCounter cc;
        const unsigned int n_threads;
};

#endif	/* !_KBFS_H_ */
