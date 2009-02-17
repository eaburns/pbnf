/**
 * \file pq.h
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-02-10
 */

#include <assert.h>

#include <iostream>

/**
 * A template priority queue class.
 */
template<class Elem, class ElemCmp, class ElemSetInd> class PriorityQueue {
public:
	PriorityQueue(void);
	void add(Elem e);
	Elem take(void);
	Elem peek(void);
	bool empty(void);
	void reset(void);
	unsigned int get_size(void);

	/** When the value of an element gets better (closer to the
	 * front of the queue) this function re-sifts it. */
	void elem_improved(int i);

	int get_fill() { return fill; }
	Elem get_elem(int i) { assert(i < fill); return heap[i]; }

private:
	int left_of(int i);
	int right_of(int i);
	int parent_of(int i);
	int is_leaf(int i);
	int max_child(int i);
	int sift_up(int i);
	int try_push(Elem e, int i);
	int sift_down(Elem e, int i);

	bool heap_holds(int, int);
	//bool indexes_match(void);

	int fill;
	int size;
	Elem* heap;
	ElemCmp cmp;
	ElemSetInd set_index;
};

template<class Elem, class ElemCmp, class ElemSetInd>
	PriorityQueue<Elem, ElemCmp, ElemSetInd>::PriorityQueue(void)
{
	heap = NULL;
	reset();
}

template<class Elem, class ElemCmp, class ElemSetInd>
	 int PriorityQueue<Elem, ElemCmp, ElemSetInd>::left_of(int i)
{
	return 2 * i + 1;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	 int PriorityQueue<Elem, ElemCmp, ElemSetInd>::right_of(int i)
{
	return 2 * i + 2;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::parent_of(int i)
{
	return (i - 1) / 2;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::is_leaf(int i)
{
	return left_of(i) >= fill && right_of(i) >= fill;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::max_child(int i)
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

template<class Elem, class ElemCmp, class ElemSetInd>
	 int PriorityQueue<Elem, ElemCmp, ElemSetInd>::sift_up(int i)
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

template<class Elem, class ElemCmp, class ElemSetInd>
	int PriorityQueue<Elem, ElemCmp, ElemSetInd>::try_push(Elem e, int i)
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

template<class Elem, class ElemCmp, class ElemSetInd>
	int  PriorityQueue<Elem, ElemCmp, ElemSetInd>::sift_down(Elem e, int i)
{
	i = try_push(e, i);
	assert(i < fill);
	heap[i] = e;
	set_index(e, i);
	assert(i < fill);

	return i;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::add(Elem e)
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

template<class Elem, class ElemCmp, class ElemSetInd>
	Elem PriorityQueue<Elem, ElemCmp, ElemSetInd>::take(void)
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

template<class Elem, class ElemCmp, class ElemSetInd>
	Elem PriorityQueue<Elem, ElemCmp, ElemSetInd>::peek(void)
{
	if (fill <= 0)
		return NULL;

	return heap[0];
}

template<class Elem, class ElemCmp, class ElemSetInd>
	 bool PriorityQueue<Elem, ElemCmp, ElemSetInd>::empty(void)
{
	return fill <= 0;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::reset(void)
{
	fill = 0;
	size = 100;
	if (heap)
		delete[] heap;
	heap = new Elem[size];
}

template<class Elem, class ElemCmp, class ElemSetInd>
	 unsigned int PriorityQueue<Elem, ElemCmp, ElemSetInd>::get_size(void)
{
	return size;
}

template<class Elem, class ElemCmp, class ElemSetInd>
	void PriorityQueue<Elem, ElemCmp, ElemSetInd>::elem_improved(int i)
{
	//assert(indexes_match());
	assert(i >= 0);
	assert(i < fill);
	Elem e = heap[i];
	set_index(e, sift_up(i));
	//assert(indexes_match());
/*
	assert(heap_holds(0, fill - 1));
*/
}

template<class Elem, class ElemCmp, class ElemSetInd>
	bool PriorityQueue<Elem, ElemCmp, ElemSetInd>::heap_holds(int ind_start, int ind_end)
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
template<class Elem, class ElemCmp, class ElemSetInd>
	bool PriorityQueue<Elem, ElemCmp, ElemSetInd>::indexes_match(void)
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
