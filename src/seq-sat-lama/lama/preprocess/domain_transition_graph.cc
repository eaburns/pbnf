/*********************************************************************
 * Authors: Malte Helmert (helmert@informatik.uni-freiburg.de),
 *          Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2003-2004 Malte Helmert and Silvia Richter
 *
 * This file is part of LAMA.
 *
 * LAMA is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 3
 * of the license, or (at your option) any later version.
 *
 * LAMA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 *
 *********************************************************************/

 
/* Unary operators are constructed in "build_DTGs" by calling 
 * "addTransition" with the appropriate arguments: for every 
 * pre-postcondition pair of an operator, an edge in the 
 * DTG is built between the corresponding values in the dtg of the
 * variable, annotated with all prevail conditions and preconditions and
 * effect conditions of that postcondition.
 */

#include "domain_transition_graph.h"
#include "operator.h"
#include "axiom.h"
#include "variable.h"
#include "scc.h"

#include <algorithm>
#include <cassert>
#include <iostream>
using namespace std;

DomainTransitionGraph::DomainTransitionGraph(const Variable &var) {
  vertices.resize(var.get_range());
  level = var.get_level();
  assert(level != -1);
}

void DomainTransitionGraph::addTransition(int from, int to, const Operator &op,
					  int op_index) {
  Transition trans(to, op_index);
  Condition &cond = trans.condition;
  const vector<Operator::Prevail> &prevail = op.get_prevail();
  const vector<Operator::PrePost> &pre_post = op.get_pre_post();
  for(int i = 0; i < prevail.size(); i++)
    if(true) // [cycles]
    // if(prevail[i].var->get_level() < level) // [no cycles]
      cond.push_back(make_pair(prevail[i].var, prevail[i].prev));
  for(int i = 0; i < pre_post.size(); i++)
    if(pre_post[i].var->get_level() != level && pre_post[i].pre != -1) // [cycles]
    // if(pre_post[i].var->get_level() < level && pre_post[i].pre != -1) //[no cycles]
      cond.push_back(make_pair(pre_post[i].var, pre_post[i].pre));
    else
      if(pre_post[i].var->get_level() == level && pre_post[i].is_conditional_effect)
	for(int j = 0; j < pre_post[i].effect_conds.size(); j++)
	  cond.push_back(make_pair(pre_post[i].effect_conds[j].var,
				   pre_post[i].effect_conds[j].cond));
	
  vertices[from].push_back(trans);
}
void DomainTransitionGraph::addAxTransition(int from, int to, const Axiom &ax,
					    int ax_index) {
  Transition trans(to, ax_index);
  Condition &cond = trans.condition;
  const vector<Axiom::Condition> &ax_conds = ax.get_conditions();
  for(int i = 0; i < ax_conds.size(); i++)
    if(true) // [cycles]
    // if(prevail[i].var->get_level() < level) // [no cycles]
      cond.push_back(make_pair(ax_conds[i].var, ax_conds[i].cond));
  vertices[from].push_back(trans);
}

bool DomainTransitionGraph::Transition::operator<(const Transition &other) const {
  if (target != other.target)
    return target < other.target;
  else
    return condition.size() < other.condition.size();
}

void DomainTransitionGraph::finalize() {
  for(int i = 0; i < vertices.size(); i++) {
    // For all sources, sort transitions according to targets and condition length
    sort(vertices[i].begin(), vertices[i].end());
    vertices[i].erase(unique(vertices[i].begin(), vertices[i].end()),
		      vertices[i].end());
    // For all transitions, sort conditions (acc. to pointer addresses)
    for(int j = 0; j < vertices[i].size(); j++) {  
      Transition &trans = vertices[i][j];
      Condition &cond = trans.condition;
      sort(cond.begin(), cond.end());
    }
    // Look for dominated transitions
    vector<Transition> undominated_trans;
    vector<bool> is_dominated;
    is_dominated.resize(vertices[i].size(), false);
    for(int j = 0; j < vertices[i].size(); j++) {
      if(!is_dominated[j]) {
	Transition &trans = vertices[i][j];
	undominated_trans.push_back(trans);
	Condition &cond = trans.condition;
	int comp = j + 1; // compare transition no. j to no. comp
	// comp is dominated if it has same target and same and more conditions
	while(comp < vertices[i].size()) {
	  if(is_dominated[comp]) {
	    comp++;
	    continue;
	  }
	  Transition &other_trans = vertices[i][comp];
	  assert(other_trans.target >= trans.target);
	  if(other_trans.target != trans.target)
	    break; // transition and all after it have different targets
	  else { //domination possible
	    assert(other_trans.condition.size() >= cond.size());
	    if(cond.size() == 0) {
	      is_dominated[comp] = true; // comp is dominated
	      comp++;
	    }	      
	    else {
	      bool same_conditions = true;
	      for(int k = 0; k < cond.size(); k++) {
		bool cond_k = false;
		for(int l = 0; l < other_trans.condition.size(); l++) {
		  if(other_trans.condition[l].first > cond[k].first){
		    break; // comp doesn't have this condition, not dominated
		  }
		  if(other_trans.condition[l].first == cond[k].first &&
		     other_trans.condition[l].second == cond[k].second) {
		    cond_k = true;
		    break; // comp has this condition, look for next cond
		  }
		}
		if(!cond_k) { // comp is not dominated
		  same_conditions = false; 
		  break;
		}
	      }
	      is_dominated[comp] = same_conditions;
	      comp++;
	    }
	  }
	}
      }
    }
  }
}

void build_DTGs(const vector<Variable *> &var_order,
		const vector<Operator> &operators,
		const vector<Axiom> &axioms,
		vector<DomainTransitionGraph> &transition_graphs) {
  for(int i = 0; i < var_order.size(); i++) {
    transition_graphs.push_back(DomainTransitionGraph(*var_order[i]));
  }

  for(int i = 0; i < operators.size(); i++) {
    const Operator &op = operators[i];
    const vector<Operator::PrePost> &pre_post = op.get_pre_post();
    for(int j = 0; j < pre_post.size(); j++) {
      const Variable *var = pre_post[j].var;
      int var_level = var->get_level();
      if(var_level != -1) {
	int pre = pre_post[j].pre;
	int post = pre_post[j].post;
	if(pre != -1) {
	  transition_graphs[var_level].addTransition(pre, post, op, i);
	} else {
	  for(int pre = 0; pre < var->get_range(); pre++)
	    if(pre != post)
	      transition_graphs[var_level].addTransition(pre, post, op, i);
	}
      }
      //else
	 //cout <<"leave out var "<< var->get_name()<<" (unimportant) " << endl;
    }
  }
  for(int i = 0; i < axioms.size(); i++) {
    const Axiom &ax = axioms[i];
    Variable *var = ax.get_effect_var();
    int var_level = var->get_level();
    assert(var_level != -1);
    int old_val = ax.get_old_val();
    int new_val = ax.get_effect_val();
    transition_graphs[var_level].addAxTransition(old_val, new_val, ax, i);
  }    

  for(int i = 0; i < transition_graphs.size(); i++)
    transition_graphs[i].finalize();
}
bool are_DTGs_strongly_connected(const vector<DomainTransitionGraph> &transition_graphs) {
  bool connected = true;
  // no need to test last variable's dtg (highest level variable)
  for(int i = 0; i < transition_graphs.size() - 1; i++)
    if(!transition_graphs[i].is_strongly_connected())
      connected = false;
  return connected;
}
bool DomainTransitionGraph::is_strongly_connected() const {
  vector<vector<int> > easy_graph;
  for(int i = 0; i < vertices.size(); i++) {
    vector<int> empty_vector;
    easy_graph.push_back(empty_vector);
    for(int j = 0; j < vertices[i].size(); j++) {
      const Transition &trans = vertices[i][j];
      easy_graph[i].push_back(trans.target);
    }
  }
  vector<vector<int> > sccs = SCC(easy_graph).get_result();
 //  cout << "easy graph sccs for var " << level << endl;
//   for(int i = 0; i < sccs.size(); i++) {
//     for(int j = 0; j < sccs[i].size(); j++)
//       cout << " " << sccs[i][j];
//     cout << endl;
//   }
  bool connected = false;
  if(sccs.size() == 1){
    connected = true;
    //cout <<"is strongly connected" << endl;
  }
  //else cout << "not strongly connected" << endl;
  return connected;
}
void DomainTransitionGraph::dump() const {
  cout << "Level: " << level << endl;
  for(int i = 0; i < vertices.size(); i++) {
    cout << "  From value " << i << ":" << endl;
    for(int j = 0; j < vertices[i].size(); j++) {
      const Transition &trans = vertices[i][j];
      cout << "    " << "To value " << trans.target << endl;
      for(int k = 0; k < trans.condition.size(); k++)
	cout << "      if " << trans.condition[k].first->get_name()
	     << " = " << trans.condition[k].second << endl;
    }
  }
}

void DomainTransitionGraph::generate_cpp_input(ofstream &outfile) const {
  //outfile << vertices.size() << endl; // the variable's range
  for(int i = 0; i < vertices.size(); i++) {
    outfile << vertices[i].size() << endl; // number of transitions from this value
    for(int j = 0; j < vertices[i].size(); j++) {
      const Transition &trans = vertices[i][j];
      outfile << trans.target << endl;  // target of transition
      outfile << trans.op << endl; // operator doing the transition
      // calculate number of important prevail conditions
      int number = 0;
      for(int k = 0; k < trans.condition.size(); k++)
	if(trans.condition[k].first->get_level() != -1)
	  number++;
      outfile << number << endl; 
      for(int k = 0; k < trans.condition.size(); k++)
	if(trans.condition[k].first->get_level() != -1)
	  outfile << trans.condition[k].first->get_level() <<
	    " " << trans.condition[k].second << endl; // condition: var, val
    }
  }
}

