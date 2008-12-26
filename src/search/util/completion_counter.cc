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

using namespace std;

CompletionCounter::CompletionCounter(unsigned int max)
	: counter(0), max(max)
{
	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
}

CompletionCounter::CompletionCounter(void)
	: counter(0), max(0)
{
	pthread_mutex_init(&mutex, NULL);
	pthread_cond_init(&cond, NULL);
}

/**
 * Set the maximum value.
 */
void CompletionCounter::set_max(unsigned int max)
{
	pthread_mutex_lock(&mutex);
	this->max = max;
	pthread_mutex_unlock(&mutex);
}

unsigned int CompletionCounter::get_count()
{
	unsigned int ret;
	pthread_mutex_lock(&mutex);
	ret = counter;
	pthread_mutex_unlock(&mutex);
        return ret;
}

bool CompletionCounter::is_complete()
{
	bool ret;
	pthread_mutex_lock(&mutex);
	ret = counter >= max;
	pthread_mutex_unlock(&mutex);
        return ret;
}

void CompletionCounter::complete(void)
{
	cout << "completing" << endl;
	pthread_mutex_lock(&mutex);
	counter += 1;
	cout << "completed " << counter << " of " << max << endl;
	//pthread_cond_signal(&cond);
	pthread_mutex_unlock(&mutex);
}

void CompletionCounter::uncomplete(void)
{
	pthread_mutex_lock(&mutex);
	counter -= 1;
	pthread_mutex_unlock(&mutex);
}

/**
 * Wait for all the completions. (counter == max)
 */
void CompletionCounter::wait(void)
{
	pthread_mutex_lock(&mutex);
	while (counter < max)
	  {}//pthread_cond_wait(&cond, &mutex);
	//doing busy wait now
	pthread_mutex_unlock(&mutex);
}

/**
 * Reset the counter to zero.
 */
void CompletionCounter::reset(void)
{
	pthread_mutex_lock(&mutex);
	counter = 0;
	pthread_mutex_unlock(&mutex);
}
