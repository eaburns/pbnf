/* -*- mode:linux -*- */
/**
 * \file synch_pq_olist.cc
 *
 * A thread Synch Priority queue OpenList implementation.
 *
 * \author Ethan Burns
 * \date 2008-10-10
 */

#include <pthread.h>

#include "synch_pq_olist.h"

SynchPQOList::SynchPQOList(void) {
	pthread_mutex_init(&mutex, NULL);
}

void SynchPQOList::add(State *s)
{
	pthread_mutex_lock(&mutex);
	PQOpenList::add(s);
	pthread_mutex_unlock(&mutex);
}

State *SynchPQOList::take(void)
{
	State *ret;

	pthread_mutex_lock(&mutex);
	ret = PQOpenList::take();
	pthread_mutex_unlock(&mutex);

	return ret;
}

State *SynchPQOList::peek(void)
{
	State *ret;

	pthread_mutex_lock(&mutex);
	ret = PQOpenList::peek();
	pthread_mutex_unlock(&mutex);

	return ret;
}

bool SynchPQOList::empty(void)
{
	bool ret;

	pthread_mutex_lock(&mutex);
	ret = PQOpenList::empty();
	pthread_mutex_unlock(&mutex);

	return ret;
}

void SynchPQOList::delete_all_states(void)
{
	pthread_mutex_lock(&mutex);
	PQOpenList::delete_all_states();
	pthread_mutex_unlock(&mutex);
}
