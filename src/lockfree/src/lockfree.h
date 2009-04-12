/**
 * \file lockfree.h
 *
 * A header file for all of the global lock free functions.
 *
 * \author eaburns
 * \date 2009-03-19
 */
#if !defined(_LOCKFREE_H_)
#define _LOCKFREE_H_

/*
 *************************************************************
 */

struct lf_queue;

/**
 * Create a new lock free queue.
 *
 * \param nbrelm The maximum number of elements that can go on this queue.
 *
 * \return A new queue or NULL and errno is set.
 */
struct lf_queue *lf_queue_create(size_t nbrelm);

/**
 * Destroy and free the memory from a previously allocated lock free queue.
 */
void lf_queue_destroy(struct lf_queue *queue);

/**
 * Add the given element to the queue.
 *
 * \param elm A pointer that must not be NULL.
 *
 * \return 0 on success, !0 on failure and errno is set.
 */
int lf_queue_enqueue(struct lf_queue *queue, void *elm);

/**
 * Remove and return the front element of the queue.
 *
 * \return NULL if empty, or else the value at the head of the queue.
 */
void *lf_queue_dequeue(struct lf_queue *queue);

/**
 * Test if the queue is empty.
 */
int lf_queue_empty(struct lf_queue *queue);

/*
 *************************************************************
 */

struct lf_ordlist;

/**
 * Create a new ordered list that can hold up to 'nbrelm' elements.
 */
struct lf_ordlist *lf_ordlist_create(size_t nbrelm,
				     int (*cmp)(void *a, void *b));

/**
 * Destroy an ordered list and all of the memory that was allocated
 * for it.
 */
void lf_ordlist_destroy(struct lf_ordlist *lst);

/**
 * Test if the given orederd list is empty.
 */
int lf_ordlist_empty(struct lf_ordlist *lst);

/**
 * Find the element in the ordlist whose value compares equal to the
 * given value.
 *
 * \return NULL if it is not found.
*/
void *lf_ordlist_find(struct lf_ordlist *lst, void *value);

/**
 * Add the given value to the ordlist.
 *
 * \return !0 if this call just added the element, 0 if someone else
 *         got to it first.
 */
int lf_ordlist_add(struct lf_ordlist *lst, void *value);

/**
 * Remove the element with the given value from the list.
 *
 * \return !0 if this call just removed the element, 0 if someone else
 *         got to it first.
 */
int lf_ordlist_remove(struct lf_ordlist *lst, void *value);


/**
 * Print the ordered list to the given file.
 *
 * This is in no way atomic, lock-free, wait-free or even thread
 * safe... it is just to be used for debugging the list.
 */
void lf_ordlist_print(FILE *f, struct lf_ordlist *lst);

/*
 *************************************************************
 */

/**
 * Create a new lock free priority queue.
 *
 * \param nbrelm The max number of elements that will be added to the queue.
 *
 * \param pred The predecessor function.  This function takes two
 *             values and returns true if the first value comes before
 *             the second.
 *
 * \return The new pq on success, NULL on error and errno is set.
 */
struct lf_pq *lf_pq_create(size_t nbrelm, int (*pred)(void*, void*));

/**
 * Destroy the given priority queue and free all of its memory.
 */
void lf_pq_destroy(struct lf_pq *pq);

/**
 * Insert a value into the priority queue.
 *
 * \return !0 on error, erron is set and 0 on success.
 */
int lf_pq_insert(struct lf_pq *pq, void *val);

/**
 * Get and remove the minimum value from the priority queue.
 *
 * \return NULL if the queue was empty, the value of the minimum entry
 *         if not.
 */
void *lf_pq_delete_min(struct lf_pq *pq);

/**
 * Test if the PQ is empty.
 */
int lf_pq_empty(struct lf_pq *pq);

/**
 * This is in no way thread safe.
 */
void lf_pq_print(FILE *f, struct lf_pq *pq);

/**
 * Test that the priority queue holds.  If there is an error, some
 * info about it is printed to the given file.
 *
 * This is in no way thread safe.
 */
int lf_pq_property_holds(FILE *f, struct lf_pq *pq);

/*
 *************************************************************
 */

#endif	/* !_LOCKFREE_H_ */
