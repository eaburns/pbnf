/**
 * \file nblock_map.h
 *
 * A map from unsigned int ids no nblocks where the nblocks are
 * created lazily upon request.
 *
 * \author Ethan Burns
 * \date 2009-02-18
 */

#if !defined(_NBLOCK_MAP_H_)
#define _NBLOCK_MAP_H_

#include <pthread.h>

#include "../projection.h"

template<class NB> class NBlockMap {
public:
	NBlockMap(const Projection *p);
	~NBlockMap(void);

	NB *get(unsigned int);

	NB *find(unsigned int);

	unsigned int get_num_created(void);

private:
	const Projection *project;
	NB **blocks;
	unsigned int num_nblocks;
	unsigned int num_created;
	pthread_mutex_t mutex;
};

/**
 * Create a new NBlockMap that creates nblocks using the given
 * projection function.
 */
template<class NB>
NBlockMap<NB>::NBlockMap(const Projection *p)
{
	project = p;
	num_nblocks = p->get_num_nblocks();
	blocks = new NB*[num_nblocks];
	for (unsigned int i = 0; i < num_nblocks; i += 1)
		blocks[i] = NULL;
	num_created = 0;
	pthread_mutex_init(&mutex, NULL);
}

/**
 * Destruct the nblock map and delete all of its nblocks.
 */
template<class NB>
NBlockMap<NB>::~NBlockMap(void)
{
	for (unsigned int i = 0; i < num_nblocks; i += 1)
		if (blocks[i])
			delete blocks[i];
	delete[] blocks;
}

/**
 * Get the NBlock with the given ID.  If the NBlock is not yet
 * created, then create it.
 */
template<class NB>
NB *NBlockMap<NB>::get(unsigned int id)
{
	if (!blocks[id]) {
		pthread_mutex_lock(&mutex);
		if (!blocks[id]) {
			blocks[id] = new NB(project, id);
			num_created += 1;
		}
		pthread_mutex_unlock(&mutex);
	}

	return blocks[id];
}

/**
 * Get the NBlock with the given ID if it has already been created, if
 * not return NULL.
 */
template<class NB>
NB *NBlockMap<NB>::find(unsigned int id)
{
	return blocks[id];
}

/**
 * Get the number of nblocks that were actually created.
 */
template<class NB>
unsigned int NBlockMap<NB>::get_num_created(void)
{
	return num_created;
}
#endif /* !_NBLOCK_MAP_H_ */
