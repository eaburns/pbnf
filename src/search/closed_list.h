/* -*- mode:linux -*- */
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

#include <vector>

#include "state.h"

using namespace std;

/**
 * A simple closed list class.
 */
class ClosedList {
public:
	ClosedList(void);
	ClosedList(unsigned long size);
	~ClosedList(void);
	void add(const State *);
	const State *lookup(const State *);
	void delete_all_states(void);

private:
	void init(unsigned long size);
	void new_table(void);
	void resize(void);
	void do_add(const State *s);
	unsigned long get_ind(const State *s);

	class Bucket {
	public:
		Bucket(const State *data, Bucket *next);
		~Bucket(void);

		const State *lookup(const State *s);
		Bucket *add(const State *s);

		const State *data;
		Bucket *next;
		unsigned int size;
	};

	vector<Bucket *> *table;
	unsigned long size;
	unsigned long fill;
};

#endif	/* !_CLOSED_LIST_H_ */
