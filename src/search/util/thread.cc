/* -*- mode:linux -*- */
/**
 * \file thread.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include <pthread.h>
#include <limits.h>
#include <string.h>

#include <iostream>

#include "thread.h"

using namespace std;

#if !defined(LINE_MAX)
#if !defined(_POSIX2_LINE_MAX)
#define LINE_MAX 2048
#else  // !_POSIX2_LINE_MAX
#define LINE_MAX _POSIX2_LINE_MAX
#endif	// _POSIX2_LINE_MAX
#endif	// LINE_MAX

unsigned int Thread::next_id = 0;

/**
 * Create a new thread.
 */
Thread::Thread(void)
{
	id = next_id;
	next_id += 1;
}

/**
 * Pthreads can't call methods of a class directly.  This function
 * just calls the run method of the class that is passed in as the
 * parameter.
 */
void *pthread_call_run(void *void_t)
{
	Thread *t = (Thread *) void_t;

	t->run();

	return NULL;
}

/**
 * Virtual destructor... apparently.
 */
Thread::~Thread(void) {}

/**
 * Joins the thread.  This means that it waits for the thread to exit.
 * \return 0 on success, a negative error value on error.
 */
int Thread::join(void) const
{
	return pthread_join(pthread_id, NULL);
}

/**
 * Get the ID that the system uses to identfy the thread.
 */
pthread_t Thread::get_sys_id(void) const
{
	return pthread_id;
}

/**
 * Get the ID of this thread.
 */
unsigned int Thread::get_id(void) const
{
	return id;
}

/**
 * Start the new thread.
 */
int Thread::start(void)
{
	int ret;
	char buf[LINE_MAX];

	ret = pthread_create(&pthread_id, NULL, pthread_call_run, this);
	if (ret < 0) {
		strerror_r(ret, buf, LINE_MAX);
		cerr << "Error starting thread: " << buf << endl;
	}

	return ret;
}
