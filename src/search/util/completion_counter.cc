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
}

CompletionCounter::CompletionCounter(void)
	: counter(0), max(0)
{
}

/**
 * Set the maximum value.
 */
void CompletionCounter::set_max(unsigned int max)
{
	this->max = AtomicInt(max);
}

unsigned int CompletionCounter::get_count()
{
	unsigned int ret;
	ret = counter.read();
        return ret;
}

bool CompletionCounter::is_complete()
{
	bool ret;
	ret = counter.read() >= max.read();
        return ret;
}

void CompletionCounter::complete(void)
{
	counter.add(1);
}

void CompletionCounter::uncomplete(void)
{
	counter.sub(1);
}

/**
 * Wait for all the completions. (counter == max)
 */
void CompletionCounter::wait(void)
{
	while (counter.read() < max.read())
	  {}//pthread_cond_wait(&cond, &mutex);
	//doing busy wait now
}

/**
 * Reset the counter to zero.
 */
void CompletionCounter::reset(void)
{
	counter = AtomicInt(0);
}
