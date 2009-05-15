/**
 * \file timeout.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-12-16
 */

#include <iostream>

#include <string.h>
#include <signal.h>
#include <stdlib.h>
#include <unistd.h>

using namespace std;

static volatile bool timeout_stopped = false;

extern "C" void alarm_action(int sig)
{
	if (timeout_stopped)
		return;

	cout << "# Time out" << endl
	     << "cost: infinity" << endl
	     << "length: infinity" << endl
	     << "wall_time: infinity" << endl
	     << "CPU_time: infinity" << endl
	     << "generated: infinity" << endl
	     << "expanded: infinity" << endl;

	exit(EXIT_SUCCESS);
}

void timeout(unsigned int sec)
{
	struct sigaction sa;

	memset(&sa, '\0', sizeof(sa));

	sa.sa_handler = alarm_action;
	sigfillset(&sa.sa_mask);
	sigaction(SIGALRM, &sa, NULL);

	timeout_stopped = false;
	alarm(sec);
}

void timeout_stop(void)
{
	timeout_stopped = true;
}
