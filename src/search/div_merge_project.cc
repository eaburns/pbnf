/* -*- mode:linux -*- */
/**
 * \file div_merge_project.cc
 *
 *
 *
 * \author Ethan Burns
 * \date 2008-12-19
 */

#include <vector>

#include "div_merge_project.h"

using namespace std;

DivMergeProject::DivMergeProject(unsigned int div, Projeciton *p)
	: div(div), projection(p) {}

unsigned int DivMergeProject::project(State *s)
{
	return projection->project(s) / div;
}

unsigned int DivMergeProject::get_num_nblocks(void)
{
	return projection->get_num_nblocks() / div;
}

vector<unsigned int> DivMergeProject::get_successors(unsigned int b)
{
	set<unsigned int> s;

}

vector<unsigned int> DivMergeProject::get_predecessors(unsigned int b)
{
	set<unsigned int> s;

}
