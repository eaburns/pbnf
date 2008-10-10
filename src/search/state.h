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

#include <iostream>
#include <vector>

#include "search_domain.h"

using namespace std;

/**
 * An abstract search state class.
 */
class State {
public:
	State(const SearchDomain *d, const State *parent, int g);

	virtual int hash(void) const = 0;
	virtual bool is_goal(void) const = 0;
	virtual State *clone(void) const = 0;
	virtual void print(ostream &o) const = 0;

	virtual vector<const State*> *expand(void) const;

	virtual float get_f(void) const;
	virtual float get_g(void) const;
	virtual float get_h(void) const;
	virtual vector<const State *> *get_path(void) const;
protected:
	const State *parent;
	const SearchDomain *domain;
	float g;
	float h;
};

#endif	/* !_STATE_H_ */
