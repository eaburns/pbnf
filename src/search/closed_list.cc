/* -*- mode:linux -*- */
/**
 * \file closed_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <assert.h>

#include <vector>

#include "state.h"
#include "closed_list.h"

ClosedList::Bucket::Bucket(const State *data, ClosedList::Bucket *next)
{
	this->data = data;
	this->next = next;
	if (!next)
		size = 0;
	else
		size = next->size + 1;
}

ClosedList::Bucket::~Bucket(void)
{
	if (next)
		delete next;
}

const State *ClosedList::Bucket::lookup(const State *s)
{
	if (s->hash() == data->hash())
		return data;
	else if (data->hash() > s->hash())
		return NULL;
	else if (!next)
		return NULL;

	return next->lookup(s);
}

ClosedList::Bucket *ClosedList::Bucket::add(const State *s)
{
	if (s->hash() < data->hash())
		return new Bucket(s, this);
	else if (s->hash () == data->hash())
		data = s;
	else if (!next)
		next = new Bucket(s, NULL);
	else {
		next = next->add(s);
		size += 1;
	}

	return this;
}

void ClosedList::init(unsigned long size)
{
	this->size = size;
	fill = 0;
}

ClosedList::ClosedList(void)
{
	init(1000000);
}

ClosedList::ClosedList(unsigned long size)
{
	init(size);
}

ClosedList::~ClosedList(void)
{
	vector<Bucket*>::iterator iter;

	if (!table)
		return;

	for (iter = table->begin(); iter != table->end(); iter++)
		if (*iter)
			delete *iter;
	delete table;
}

/**
 * Initializes the table if it hasn't been created yet
 */
void ClosedList::new_table(void)
{
	if (!table) {
		table = new vector<Bucket *>();
		table->resize(size);
	}
}

/**
 * Add to the closed list.
 * \param s The state to add.
 */
void ClosedList::add(const State *s)
{
	new_table();
	if (fill + 1 >= size / 3)
		resize();

	do_add(s);
	fill += 1;
}

/**
 * Grow the table and rehash everything.
 */
void ClosedList::resize(void)
{
	Bucket *b;
	vector<Bucket*>::iterator iter;
	vector<Bucket*> *old_table = table;

//	cerr << "resize" << endl;

	table = new vector<Bucket *>();
	size = size * 10;
	table->resize(size, NULL);

	for (iter = old_table->begin(); iter != old_table->end(); iter++) {
		for (b = *iter; b; b = b->next)
			do_add(b->data);
		if (*iter)
			delete *iter;
	}

	delete old_table;
}

/**
 * Get the table index for the given state.
 */
unsigned long ClosedList::get_ind(const State *s)
{
	return s->hash() % size;
}

/**
 * Add a state to the table.
 */
void ClosedList::do_add(const State *s)
{
	Bucket *old = table->at(get_ind(s));
	if (!old)
		table->at(get_ind(s)) = new Bucket(s, NULL);
	else
		table->at(get_ind(s)) = old->add(s);

/*
	if (table->at(get_ind(s))->size > 3)
		cerr << "size: " <<  table->at(get_ind(s))->size
		     << " fill: " << fill << endl;
*/
}

/**
 * Lookup a state in the closed list.
 * \param c The state to look up.
 * \return The state if it was found, NULL on error.
 */
const State *ClosedList::lookup(const State *c)
{
	if (!table)
		return NULL;

	if (table->at(get_ind(c)))
		return table->at(get_ind(c))->lookup(c);
	else
		return NULL;
}

/**
 * Delete (free up the memory for) all states in the closed list.
 */
void ClosedList::delete_all_states(void)
{
	Bucket *b;
	vector<Bucket*>::iterator iter;

	if (!table)
		return;

	for (iter = table->begin(); iter != table->end(); iter++)
		for (b = *iter; b; b = b->next)
			delete b->data;
}
