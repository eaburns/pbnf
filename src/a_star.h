/**
 * \file a_star.h
 *
 * Contains the AStar class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_A_STAR_H_)
#define _A_STAR_H_

#include "state.h"
#include "search.h"
#include "closed_list.h"

/**
 * An A* search class.
 */
class AStar : public Search {
public:
	AStar(void);
	AStar(bool dd);
	virtual ~AStar(void);
	virtual vector<State *> *search(Timer *, State *);
private:
	ClosedList closed;
	bool dd;		/* dup dropping */
};

#endif	/* !_A_STAR_H_ */
