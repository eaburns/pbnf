/* -*- mode:linux -*- */
/**
 * \file timer.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-11-03
 */

#if !defined(_TIMER_H_)
#define _TIMER_H_

class Timer {
public:
	void start(void);
	double stop(void);
private:
	double start_time;
};

#endif	/* !_TIMER_H_ */
