/**
 * \file lpastar.cc
 *
 *
 *
 * \author Ethan Burns (modified from Seth Lemons' pastar.cc)
 * \date 2009-04-12
 */

#include "util/thread.h"
#include "state.h"
#include "lpastar.h"

class LPAStarThread : public Thread {
public:
	LPAStarThread() {}
	LPAStarThread(LPAStar *p) : p(p) {}
	LPAStarThread(LPAStar *p, AtomicInt* working) : p(p), working(working) {}

	virtual void run(void){
		vector<State *> *children = NULL;
		State *s;

		while(!p->is_done()){
			if(!p->open.empty()){
				s = p->open.take();
				if (!s)
					continue;
			} else{
				working->dec();
				if (p->open.empty() && working->read() == 0) {
					p->set_done();
					break;
				}

				while(p->open.empty() && working->read() != 0)
					;

				if (p->open.empty() && working->read() == 0)
					break;

				working->inc();
				continue;
			}

			if (s->get_f() >= p->bound.read())
				continue;

			State *dup = p->closed.lookup(s);
			if (dup && dup->get_g() < s->get_g())
				continue;

			if (s->is_goal())
				p->set_path(s->get_path());

			children = p->expand(s);
			for (unsigned int i = 0; i < children->size(); i += 1) {
				State *c = children->at(i);
				State *dup = p->closed.lookup(c);
				if (dup) {
					if (dup->get_g() > c->get_g()) {
						p->closed.add(c);
						p->open.add(c);
					}
				} else {
					p->closed.add(c);
					p->open.add(c);
				}
			}
		}
    
		delete children;
	}
  
private:
	LPAStar *p;
	friend class LPAStar;
	AtomicInt *working;
};


LPAStar::LPAStar(unsigned int n_threads)
  : n_threads(n_threads),
    path(NULL),
    bound(fp_infinity)
{
	done = false;
}

void LPAStar::set_done()
{
        done = true;
}

bool LPAStar::is_done()
{
        return done;
}

void LPAStar::set_path(vector<State *> *p)
{
	// unfortunately have to lock here (should be the rare case).
        pthread_mutex_lock(&mutex);
        if (this->path == NULL || 
	    this->path->at(0)->get_g() > p->at(0)->get_g()){
		this->path = p;
		bound.set(p->at(0)->get_g());
        }
        pthread_mutex_unlock(&mutex);
}

bool LPAStar::has_path()
{
        return path != NULL;
}


/**
 * Perform a Parallel A* search.
 */
vector<State *> *LPAStar::search(Timer *t, State *init)
{
 	open.add(init);
        pthread_mutex_init(&mutex, NULL);

	AtomicInt working(n_threads);

        unsigned int worker;
        vector<LPAStarThread *> threads;
	vector<LPAStarThread *>::iterator iter;
        for (worker=0; worker<n_threads; worker++) {
		LPAStarThread *t = new LPAStarThread(this, &working);
		threads.push_back(t);
		t->start();
        }
	for (iter = threads.begin(); iter != threads.end(); iter++) {
		(*iter)->join();
		delete *iter;
	}

 	return path;
}
