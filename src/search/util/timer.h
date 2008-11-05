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
	Timer(void);
	void start(void);
	double stop(void);
	double get_elapsed(void);
private:
	double compute_elapsed(void);

	double start_time;
	float elapsed;
	bool running;
};

#endif	/* !_TIMER_H_ */
