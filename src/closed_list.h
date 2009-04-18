/**
 * \file closed_list.h
 *
 * A simple closed list class.
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#if !defined(_CLOSED_LIST_H_)
#define _CLOSED_LIST_H_

#include <list>

#include "state.h"

using namespace std;

/**
 * A simple closed list class.
 */
class ClosedList {
public:
	ClosedList(void);
	ClosedList(unsigned long size);
	virtual ~ClosedList(void);
	virtual void add(State *);
	virtual State *lookup(State *);
	virtual void delete_all_states(void);

	virtual void prune(void);
	virtual list<State*> *get_states();

private:
	void init(unsigned long size);
	void new_table(void);
	void resize(void);
	void do_add(State *s);
	unsigned long get_ind(State *s);

	class Bucket {
	public:
		Bucket(State *data, Bucket *next);
		~Bucket(void);

		State *lookup(State *s);
		Bucket *add(State *s);

		State *data;
		Bucket *next;
		unsigned int size;
	};

	Bucket **table;
	unsigned long size;
	unsigned long fill;
};

#endif	/* !_CLOSED_LIST_H_ */
