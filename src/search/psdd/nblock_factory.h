/* -*- mode:linux -*- */
/**
 * \file nblock_factory.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-20
 */

#if !defined(_NBLOCK_FACTORY_H_)
#define _NBLOCK_FACTORY_H_

#include "nblock.h"

class NBlockFactory {
public:
	virtual ~NBlockFactory();

	virtual NBlock *new_nblock(unsigned int hash) const = 0;
};

#endif	/* !_NBLOCK_FACTORY_H_ */
