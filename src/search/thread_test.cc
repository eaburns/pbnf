/* -*- mode:linux -*- */
/**
 * \file thread_test.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-10-21
 */

#include <iostream>

#include "util/thread.h"

using namespace std;

class TestThread : public Thread {
public:
	TestThread(int id, int num) : id(id), num(num) {}

	~TestThread() {}

	virtual void run(void) {
		for (int i = 0; i < num; i += 1)
			cout << "thread " << get_id()
			     << "(" << id << "): " << i << endl;
	}

private:
	int id;
	int num;
};


int main(void)
{
	TestThread one(1, 1000);
	TestThread two(2, 2000);

	one.start();
	two.start();

	one.join();
	cout << "one finished" << endl;

	two.join();
	cout << "two finished" << endl;

	return 0;
}
