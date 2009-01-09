/**
 * \file div_merge_project.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-12-19
 */

#include <vector>
#include <set>

#include "projection.h"
#include "div_merge_project.h"

using namespace std;

DivMergeProject::DivMergeProject(unsigned int div, Projection *p)
	: div(div), projection(p) {}

unsigned int DivMergeProject::project(State *s) const
{
	return projection->project(s) / div;
}

unsigned int DivMergeProject::get_num_nblocks(void) const
{
	return projection->get_num_nblocks() / div;
}

vector<unsigned int> DivMergeProject::get_successors(unsigned int b) const
{
	set<unsigned int> s;

	for (unsigned int i = 0; i < div; i += 1) {
		int nblk = (b * div + i);
		vector<unsigned int> succs = projection->get_successors(nblk);
		vector<unsigned int>::iterator iter;
		for (iter = succs.begin(); iter != succs.end(); iter++) {
			unsigned int suc = (*iter) / div;
			if (suc != b)
				s.insert(suc);
		}
	}

	return vector<unsigned int>(s.begin(), s.end());
}

vector<unsigned int> DivMergeProject::get_predecessors(unsigned int b) const
{
	set<unsigned int> s;

	for (unsigned int i = 0; i < div; i += 1) {
		int nblk = (b * div + i);
		vector<unsigned int> preds = projection->get_predecessors(nblk);
		vector<unsigned int>::iterator iter;
		for (iter = preds.begin(); iter != preds.end(); iter++) {
			unsigned int pred = (*iter) / div;
			if (pred != b)
				s.insert(pred);
		}
	}

	return vector<unsigned int>(s.begin(), s.end());
}

