/* -*- mode:linux -*- */
/**
 * \file synch_closed_list.h
 *
 *
 *
 * \author Seth Lemons
 * \date 2008-10-13
 */

#include <pthread.h>

#include "synch_closed_list.h"

SynchClosedList::SynchClosedList(void) {
	pthread_mutex_init(&mutex, NULL);
}

void SynchClosedList::add(const State *s)
{
	pthread_mutex_lock(&mutex);
	ClosedList::add(s);
	pthread_mutex_unlock(&mutex);
}

const State *SynchClosedList::lookup(const State *c)
{
        pthread_mutex_lock(&mutex);
	const State *s = ClosedList::lookup(c);
        pthread_mutex_unlock(&mutex);
        return s;
}

void SynchClosedList::delete_all_states(void)
{
	pthread_mutex_lock(&mutex);
	ClosedList::delete_all_states();
	pthread_mutex_unlock(&mutex);
}