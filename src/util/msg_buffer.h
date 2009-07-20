/**
 * \file msg_buffer.h
 *
 * Async communication between a producer and a consumer thread.
 *
 * The way this works is that the producer thread attempts to take the
 * lock on the recive queue of the consumer thread.  If the lock is
 * taken successfully the messages are put directly on the consumer's
 * receive queue.  If the lock fails to be taken, instead of waiting,
 * the message is buffered until a later time when it can be flushed.
 *
 * \author eaburns
 * \date 2009-07-14
 */

#if !defined(_MSG_BUFFER_H_)
#define _MSG_BUFFER_H_

#include <pthread.h>
#include <errno.h>

#include <vector>

using namespace std;

template <class Msg>
class MsgBuffer {
private:

	/**
	 * Sends a message to the remote queue.  This assumes that the
	 * caller will handle locking/unlocking the mutex.
	 */
	void __send(Msg m) {
		queue->push_back(m);
		post_send(data);
	}

	/**
	 * Flushes the buffer to the remote queue.  This assumes that
	 * the caller will handle the locking/unlocking of the mutex.
	 */
	void __flush(void) {
/*
		vector<Msg>::iterator iter;
		for(iter = buffer.begin(); iter != buffer.end(); iter++) {
			Msg m = *iter;
			__send(m);
		}
*/
		for (unsigned int i = 0; i < buffer.size(); i += 1) {
			Msg m = buffer[i];
			__send(m);
		}

		buffer.clear();
	}

public:

	/**
	 * Creates a new message buffer
	 */
	MsgBuffer(pthread_mutex_t *m, vector<Msg> *q,
		  void (*ps)(void*), void *d) {
		mutex = m;
		queue = q;
		post_send = ps;
		data = d;
	}

	/**
	 * Send a message to the remote queue.  If the lock is not
	 * available, the message is buffered until the next send
	 * occurs, or a flush operation is performed.
	 */
	bool try_send(Msg m) {
		if (pthread_mutex_trylock(mutex) == EBUSY) {
			buffer.push_back(m);
			return false;
		} else {
			__send(m);
			pthread_mutex_unlock(mutex);
			return true;
		}
	}

	/**
	 * Force a send to the remote queue.  This will wait on the
	 * lock until it is available for the send.
	 */
	void force_send(Msg m) {
		pthread_mutex_lock(mutex);
		__send(m);
		pthread_mutex_unlock(mutex);
	}

	/**
	 * Tries to flush the queue to the remote peer.
	 */
	bool try_flush(void) {

		if (buffer.empty())
			return false;

		if (pthread_mutex_trylock(mutex) != EBUSY) {
			__flush();
			pthread_mutex_unlock(mutex);
			return true;
		}

		return false;
	}

	/**
	 * Forces a flush to the remote peer.
	 */
	void force_flush(void) {
		pthread_mutex_lock(mutex);
		__flush();
		pthread_mutex_unlock(mutex);
	}

	/**
	 * Test if the buffer is empty.
	 */
	bool is_empty(void) {
		return buffer.empty();
	}

private:
	/* The lock on the message queue. */
	pthread_mutex_t *mutex;

	/* The queue to send messages */
	vector<Msg> *queue;

	/* Called when a message is sent (with the mutex held). */
	void (*post_send)(void *);

	/* Data passed to post_send. */
	void *data;

	/* A local buffer for messages. */
	vector<Msg> buffer;
};

#endif /* _MSG_BUFFER_H_ */
