/**
 * \file backoff.h
 *
 * This performs delaying using an exponential scheme based on the one
 * used in ``A Methodology for Implementing Highly Concurrent Data
 * Objects'' -- M. Herlihy.
 *
 * \author eaburns
 * \date 2009-04-10
 */
#if !defined(_BACKOFF_H_)
#define _BACKOFF_H_

#include <time.h>

/** The max delay. */
#define DELAY_MAX 1000

/** The max delay is multiplied by this value via a loop so that we
 * never run out of bits in our 'long' datatype (even on small 32-bit
 * machines). */
#define DELAY_MULT 100

static __inline__ long backoff_init(long max)
{
	if (max > 1)
		return max / 2;

	return max;
}

/**
 * Delays for a random amount (less than [max]) and returns the new
 * max value.
 */
static __inline__ long backoff(long max)
{
	static int seeded = 0;
	static struct drand48_data rand_buf;

	int j;
	long i, delay;

	if (!seeded) {
		srand48_r(time(NULL), &rand_buf);
		seeded = 1;
	}
	lrand48_r(&rand_buf, &delay);
	assert(max != 0);
	delay %= max;

	for (j = 0; j < DELAY_MULT; j += 1) {
		for (i = 0; i < delay; i += 1)
			__asm__ __volatile__ ("");
	}

	return max < DELAY_MAX ? max * 2 : max;
}

#endif	/* !_BACKOFF_H_ */
