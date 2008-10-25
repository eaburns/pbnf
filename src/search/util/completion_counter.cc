/* -*- mode:linux -*- */
/**
 * \file completion_counter.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-24
 */

#include <pthread.h>

#include "completion_counter.h"
#include <iostream>

CompletionCounter::CompletionCounter(unsigned int max)
	: counter(0), max(max)
{
	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
}

void CompletionCounter::complete(void)
{
	pthread_mutex_lock(&mutex);
	counter += 1;
	pthread_cond_signal(&cond);
	pthread_mutex_unlock(&mutex);
}

/**
 * Wait for all the completions. (counter == max)
 */
void CompletionCounter::wait(void)
{
	pthread_mutex_lock(&mutex);
	while (counter < max)
		pthread_cond_wait(&cond, &mutex);
	pthread_mutex_unlock(&mutex);
}
