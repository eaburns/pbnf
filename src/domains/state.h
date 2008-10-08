/* -*- mode:linux -*- */
/**
 * \file state.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-08
 */
#if !defined(_STATE_H_)
#define _STATE_H_

#include <vector>

#include "search_domain.h"

using namespace std;

class State {
public:
	State(const State *parent, int g);

	virtual bool is_goal(void) const = 0;
	virtual int compare(const State *s) const = 0;
	virtual int hash(void) const = 0;
	virtual vector<const State*> *expand(const State *s) const = 0;

	virtual int get_g(void) const;
	virtual int get_h(void) const;
protected:
	const State *parent;
	int g;
	int h;
};

#endif	/* !_STATE_H_ */
