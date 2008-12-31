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
	State(SearchDomain *d, State *parent, float g);

	virtual ~State();

	virtual SearchDomain *get_domain(void) const;

	virtual uint64_t hash(void) const = 0;
	virtual bool is_goal(void) = 0;
	virtual State *clone(void) const = 0;
	virtual void print(ostream &o) const = 0;
	virtual bool equals(State *s) const = 0;

	virtual vector<State*> *expand(void);

	float get_f(void) const;
	float get_g(void) const;
	float get_h(void) const;
	State *get_parent(void) const;
	vector<State *> *get_path(void);
	void set_open(bool b);
	bool is_open(void) const;
//protected:
	State *parent;
	SearchDomain *domain;
	float g;
	float h;
	bool open;
};

#endif	/* !_STATE_H_ */
