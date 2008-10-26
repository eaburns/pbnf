/* -*- mode:linux -*- */
/**
 * \file thread.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#if !defined(_THREAD_H_)
#define _THREAD_H_

#include <pthread.h>

class Thread {
public:
	Thread(void);
	virtual ~Thread(void);

	int join(void);
	int start(void);
	pthread_t get_sys_id(void) const;
	unsigned int get_id(void) const;
        void signal(void);
        void wait(void);

	virtual void run(void) = 0;

protected:
        pthread_mutex_t mutex; //cond and mutex for thread waits
        pthread_cond_t cond;
        bool exit; //set to true in join()

private:
	friend void *pthread_call_run(void *);

	pthread_t pthread_id;
	unsigned int id;

	static unsigned int next_id;
        unsigned int signalled;
};

#endif	/* !_THREAD_H_ */
