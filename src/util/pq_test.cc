/**
 * \file pq_test.c
 *
 *
 *
 * \author Ethan Burns
 * \date 2009-02-11
 */

#include "priority_queue.h"

#include <iostream>

using namespace std;

class Int {
public:
	class IntCmp {
	public:
		int operator()(Int *a, Int *b)
		{
			return a->value - b->value;
		}

		int get_value(Int *a) {
			return a->value;
		}
	};
	class IntSetInd {
	public:
		void operator()(Int *a, int ind)
		{
			a->index = ind;
		}
	};

	Int(int v) {
		value = v;
		index = -1;
	}

	int index;
	int value;
};

/*
void print(PriorityQueue<Int*, Int::IntCmp, Int::IntSetInd> pq)
{
	for (int i = 0; i < pq.get_fill(); i += 1) {
		cout << "[" << pq.get_vec()[i]->value << "]";
	}
	cout << endl;
}
*/

void print (PriorityQueue<Int*, Int::IntCmp, Int::IntSetInd> pq) {}


int main(void)
{
	PriorityQueue<Int*, Int::IntCmp, Int::IntSetInd> pq;
	Int *one = new Int(1);
	Int *three = new Int(3);

	pq.add(one);
	pq.add(new Int(2));
	pq.add(three);
	pq.add(new Int(4));
	pq.add(new Int(5));

	print(pq);
	cout << "peek: " << pq.peek()->value << endl;
	delete pq.take();
	cout << "peek: " << pq.peek()->value << endl;
	print(pq);

	one->value = 100;
	pq.elem_improved(one->index);
	cout << "peek: " << pq.peek()->value << endl;
	print(pq);
	delete pq.take();
	cout << "peek: " << pq.peek()->value << endl;
	print(pq);
	three->value = 5;
	pq.elem_improved(three->index);
	cout << "peek: " << pq.peek()->value << endl;
	print(pq);
	delete pq.take();

	return 0;
}
