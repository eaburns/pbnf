/**
 * \file pq.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-02-10
 */

#if !defined(_PRIORITY_QUEUE_H_)
#define _PRIORITY_QUEUE_H_

#include <assert.h>

#include <iostream>

/**
 * A template priority queue class.
 */
template<class Elem, class PQOps> class PriorityQueue {
public:
	PriorityQueue(void);
	void add(Elem e);
	Elem take(void);
	Elem front(void);
	bool empty(void);
	void reset(void);

	/** When the value of an element gets better (closer to the
	 * front of the queue) this function re-sifts it. */
	void elem_changed(int i);

	int get_fill() { return fill; }
	Elem get_elem(int i) { assert(i < fill); return heap[i]; }

private:
	int left_of(int i);
	int right_of(int i);
	int parent_of(int i);
	bool is_leaf(int i);
	int max_child(int i);
	int sift_up(int i);
	int try_push(Elem e, int i);
	int sift_down(Elem e, int i);

	bool heap_holds(int, int);
	//bool indexes_match(void);

	int fill;
	int size;
	Elem* heap;
	PQOps cmp;
	PQOps set_index;
};

/**
 * Create a new priority queue.
 */
template<class Elem, class PQOps>
	PriorityQueue<Elem, PQOps>::PriorityQueue(void)
{
	heap = NULL;
	reset();
}

/**
 * Get the index of the element to the left of the element [i] in the
 * tree.
 */
template<class Elem, class PQOps>
	 int PriorityQueue<Elem, PQOps>::left_of(int i)
{
	return 2 * i + 1;
}

/**
 * Get the index of the element to the right of the element [i] in the
 * tree.
 */
template<class Elem, class PQOps>
	 int PriorityQueue<Elem, PQOps>::right_of(int i)
{
	return 2 * i + 2;
}

/**
 * Get the index of the element that is the parent of element [i] in
 * the tree.
 */
template<class Elem, class PQOps>
	int PriorityQueue<Elem, PQOps>::parent_of(int i)
{
	return (i - 1) / 2;
}

/**
 * Predicate that tests if element [i] is a leaf node.
 */
template<class Elem, class PQOps>
	bool PriorityQueue<Elem, PQOps>::is_leaf(int i)
{
	return left_of(i) >= fill && right_of(i) >= fill;
}

/**
 * Get the index of the max valued child of element [i].  Element [i]
 * must not be a leaf.
 */
template<class Elem, class PQOps>
	int PriorityQueue<Elem, PQOps>::max_child(int i)
{
	int right = right_of(i);
	int left = left_of(i);
	assert(!is_leaf(i));
	if (left < fill && right < fill) {
		if (cmp(heap[right], heap[left]) > 0)
			return right;
		else
			return left;
	} else if (left < fill) {
		return left;
	} else {
		return right;
	}
	assert(1); /* Should never reach here. */
	return -1;
}

/**
 * Sift element [i] up the tree.
 *
 * \return The new index of the element that was initially at location [i].
 *
 * \note The index of [i] must be reset explicitly by the caller after
 *       this function is called.
 */
template<class Elem, class PQOps>
	 int PriorityQueue<Elem, PQOps>::sift_up(int i)
{
	int p_ind = parent_of(i);
	Elem parent = heap[p_ind];
	Elem e = heap[i];
	while (i > 0 && cmp(e, parent) > 0) {
		heap[i] = parent;
		set_index(parent, i);
		assert(i < fill);
		i = p_ind;
		p_ind = parent_of(i);
		parent = heap[p_ind];
	}
	heap[i] = e;
	return i;
}

/**
 * Tries to push an element down the tree.
 *
 * \return The new index is returned.
 *
 * \note This function does not set the new index of the element.
 */
template<class Elem, class PQOps>
	int PriorityQueue<Elem, PQOps>::try_push(Elem e, int i)
{
	int child_i = left_of(i);
	if (child_i < fill) {
		Elem child = heap[child_i];
		int right_i = right_of(i);
		if (right_i < fill) {
			Elem right = heap[right_i];
			if (cmp(child, right) < 0) {
				child = right;
				child_i = right_i;
			}
		}
		if (cmp(e, child) > 0) {
			return i;
		} else {
			heap[i] = child;
			set_index(child, i);
			assert(i < fill);
			return try_push(e, child_i);
		}
	} else {
		return i;
	}
}

/**
 * Push an element down the tree, and set its new index.
 *
 * \return The new index.
 */
template<class Elem, class PQOps>
	int  PriorityQueue<Elem, PQOps>::sift_down(Elem e, int i)
{
	i = try_push(e, i);
	assert(i < fill);
	heap[i] = e;
	set_index(e, i);
	assert(i < fill);

	return i;
}

/**
 * Add an element to the priority queue.
 */
template<class Elem, class PQOps>
	void PriorityQueue<Elem, PQOps>::add(Elem e)
{
	if (size <= fill) {
		size = size * 2;
		Elem *new_heap = new Elem[size];
		for (int i = 0; i < fill; i += 1)
			new_heap[i] = heap[i];
		delete[] heap;
		heap = new_heap;
	}

	heap[fill] = e;
	fill += 1;
	int i = sift_up(fill - 1);
	set_index(e, i);
	assert(i < fill);
/*
	assert(indexes_match());
	assert(heap_holds(0, fill - 1));
*/
}

/**
 * Take and return the front element of the priority queue.
 */
template<class Elem, class PQOps>
	Elem PriorityQueue<Elem, PQOps>::take(void)
{
	Elem e;

	if (fill <= 0)
		return NULL;

	e = heap[0];
	set_index(e, -1);

	heap[0] = heap[fill - 1];
	heap[fill - 1] = NULL;
	fill -= 1;
	if (fill > 0)
		sift_down(heap[0], 0);

/*
	assert(indexes_match());
	assert(heap_holds(0, fill - 1));
*/

	return e;
}

/**
 * Re-sort a single element in the PQ whose value has changed.
 */
template<class Elem, class PQOps>
	void PriorityQueue<Elem, PQOps>::elem_changed(int i)
{
	//assert(indexes_match());
	assert(i >= 0);
	assert(i < fill);
	Elem e = heap[i];
	int ind = sift_up(i);
	sift_down(e, ind);
	//assert(indexes_match());
/*
	assert(heap_holds(0, fill - 1));
*/
}

/**
 * Look at the front element of the priority queue.
 */
template<class Elem, class PQOps>
	Elem PriorityQueue<Elem, PQOps>::front(void)
{
	if (fill <= 0)
		return NULL;

	return heap[0];
}

/**
 * Test for empty.
 */
template<class Elem, class PQOps>
	 bool PriorityQueue<Elem, PQOps>::empty(void)
{
	return fill <= 0;
}

/**
 * Remove all elements (if any), reset fill and the default heap size.
 */
template<class Elem, class PQOps>
	void PriorityQueue<Elem, PQOps>::reset(void)
{
	fill = 0;
	size = 100;
	if (heap)
		delete[] heap;
	heap = new Elem[size];
}


/**
 * Diagnosis function for making sure that the heap property holds.
 */
template<class Elem, class PQOps>
	bool PriorityQueue<Elem, PQOps>::heap_holds(int ind_start, int ind_end)
{
	int c;
	for (int i = ind_start; i <= ind_end; i += 1) {
		int right = right_of(i);
		int left = left_of(i);
		if (right < fill && (c = cmp(heap[i], heap[right])) < 0) {
			std::cerr << "fill: " << fill
				  << " c: " << c
				  << " right: " << right
				  << " val: " << cmp.get_value(heap[right])
				  << " i: " << i
				  << " val: " << cmp.get_value(heap[i]) << std::endl;;
			return false;
		}
		if (left < fill && (c = cmp(heap[i], heap[left])) < 0) {
			std::cerr << "fill: " << fill
				  << " c: " << c
				  <<  " left: " << left
				  << " val: " << cmp.get_value(heap[left])
				  << " i: " << i
				  << " val: " << cmp.get_value(heap[i]) << std::endl;;
			return false;
		}
	}

	return true;
}

/*
template<class Elem, class PQOps>
	bool PriorityQueue<Elem, PQOps>::indexes_match(void)
{
	for (int i = 0; i < fill; i += 1) {
		if (cmp(heap[i]) != i) {
			std::cerr << "ind=" << cmp(heap[i]) << " should be: " << i << std::endl;
			return false;
		}
	}
	return true;
}
*/
#endif /* !_PRIORITY_QUEUE_H_ */
