/**
 * \file fixed_point.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-01-16
 */

#include "stdint.h"

/* The type of a fixed point value */
typedef uint64_t fp_type;

#define fp_sqrt2 14142
#define fp_one 10000

#define fp_weight_on_g(x) (fp_one)
#define fp_weight_on_h(x) ((fp_type)(fp_one * (x)))
