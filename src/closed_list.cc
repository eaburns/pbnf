/**
 * \file closed_list.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-09
 */

#include <assert.h>
#include <stdlib.h>

#include "state.h"
#include "closed_list.h"

ClosedList::Bucket::Bucket(State *d, ClosedList::Bucket *n)
{
	data = d;
	next = n;
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

State *ClosedList::Bucket::lookup(State *s)
{
	if (s->hash() == data->hash())
		return data;
	else if (data->hash() > s->hash())
		return NULL;
	else if (!next)
		return NULL;

	return next->lookup(s);
}

ClosedList::Bucket *ClosedList::Bucket::add(State *s)
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

void ClosedList::init(unsigned long s)
{
	this->table = NULL;
	this->size = s;
	fill = 0;
}

ClosedList::ClosedList(void)
{
	init(1000000);
}

ClosedList::ClosedList(unsigned long s)
{
	init(s);
}

ClosedList::~ClosedList(void)
{
	prune();
}

/**
 * Initializes the table if it hasn't been created yet
 */
void ClosedList::new_table(void)
{
	if (!table)
		table = (Bucket **) calloc(size, sizeof(Bucket *));
}

/**
 * Add to the closed list.
 * \param s The state to add.
 */
void ClosedList::add(State *s)
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
	Bucket**old_table = table;
	unsigned int old_size;


	old_size = size;
	size = size * 10;
	table = NULL;
	new_table();

	for (unsigned int i = 0; i < old_size; i += 1) {
		for (b = old_table[i]; b; b = b->next)
			do_add(b->data);
		if (old_table[i])
			delete old_table[i];
	}

	free(old_table);
}

/**
 * Get the table index for the given state.
 */
unsigned long ClosedList::get_ind(State *s)
{
	return s->hash() % size;
}

/**
 * Add a state to the table.
 */
void ClosedList::do_add(State *s)
{
	Bucket *old = table[get_ind(s)];
	if (!old)
		table[get_ind(s)] = new Bucket(s, NULL);
	else
		table[get_ind(s)] = old->add(s);

}

/**
 * Lookup a state in the closed list.
 * \param c The state to look up.
 * \return The state if it was found, NULL on error.
 */
State *ClosedList::lookup(State *c)
{
	if (!table)
		return NULL;

	if (table[get_ind(c)])
		return table[get_ind(c)]->lookup(c);
	else
		return NULL;
}

/**
 * Delete (free up the memory for) all states in the closed list.
 */
void ClosedList::delete_all_states(void)
{
	Bucket *b;

	if (!table)
		return;

	for (unsigned int i = 0; i < size; i += 1) {
		for (b = table[i]; b; b = b->next)
			delete b->data;
		if (table[i])
			delete table[i];
		table[i] = NULL;
	}
}

/**
 * Drop all states, but don't delete them.
 */
void ClosedList::prune(void)
{
	if (!table)
		return;

	for (unsigned int i = 0; i < size; i += 1) {
		if (table[i]) {
			delete table[i];
			table[i] = NULL;
		}
	}
	free(table);

	this->table = NULL;
	fill = 0;
}

/**
 * Get a list of all of the states.
 */
list<State*> *ClosedList::get_states()
{
	list<State*> *states = new list<State*>();

	if (!table)
		return states;

	for (unsigned int i = 0; i < size; i += 1) {
		Bucket *b = table[i];
		if (!b)
			continue;
		while (b) {
			states->push_front(b->data);
			b = b->next;
		}
	}

	return states;
}

bool ClosedList::is_empty()
{
	return fill == 0;
}
