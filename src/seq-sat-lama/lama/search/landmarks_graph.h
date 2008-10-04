/*********************************************************************
 * Authors: Matthias Westphal (westpham@informatik.uni-freiburg.de),
 *          Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2008 Matthias Westphal and NICTA
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

#ifndef LANDMARKS_GRAPH_H
#define LANDMARKS_GRAPH_H

#include <vector>
#include <set>
#include <map>
#include <ext/hash_map>
#include <list>
#include <ext/hash_set>
#include <cassert>

#include "operator.h"
#include "landmarks_types.h"

using namespace __gnu_cxx;

enum edge_type {n = 4, gn = 3, r = 1, o_r = 0, ln = 2};

class LandmarkNode {
public:
    LandmarkNode(vector<int>& variables, vector<int>& values, bool disj) : 
        vars(variables), vals(values), disjunctive(disj), in_goal(false), min_cost(1) {}
    vector<int> vars;
    vector<int> vals;
    bool disjunctive; 	    
    hash_map<LandmarkNode*, edge_type, hash_pointer> parents;
    hash_map<LandmarkNode*, edge_type, hash_pointer> children;
    bool in_goal;
    int min_cost; // minimal cost of achieving operators

    hash_set<pair<int, int>, hash_int_pair> forward_orders;
  
    bool is_goal() const {return in_goal;}
    bool is_true_in_state(const State& state) const {
        if(!disjunctive)
            return state[vars[0]] == vals[0];
        else{
            bool is_true = false;
            for(unsigned int i = 0; i < vars.size(); i++)
                if(state[vars[i]] == vals[i]) {
                    is_true = true;
                    break;
                }
            return is_true;
        }
    }
};

class LandmarksGraph {
public:
    class Pddl_proposition {
    public:
        string predicate;
        vector<string> arguments;
        string to_string() const {
            string output = predicate;
            for(unsigned int i = 0; i < arguments.size(); i++) {
                output += " ";
                output += arguments[i];
            }
            return output;
        }
    };

    LandmarksGraph();
    virtual ~LandmarksGraph() {};
    void read_external_inconsistencies();
    void use_reasonable_orders() {reasonable_orders = true;}

    void generate();
    bool simple_landmark_exists(const pair<int, int>& lm) const;
    bool disj_landmark_exists(const set<pair<int, int> >& lm) const;
    bool landmark_exists(const pair<int, int>& lm) const; 
    bool exact_same_disj_landmark_exists(const set<pair<int, int> >& lm) const;

    const LandmarkNode* landmark_reached(const pair<int, int>& prop) const;

    void dump_node(const LandmarkNode* node_p) const; 
    void dump() const;
    inline int cost_of_landmarks() const {
	return landmarks_cost;
    }
    inline int number_of_landmarks() const {
        return landmarks_count;
    }
    int number_of_disj_landmarks() const {
        return landmarks_count - simple_lms_to_nodes.size();
    }
    int number_of_edges() const;

    inline LandmarkNode& get_simple_lm_node(const pair<int, int>& a) const {
        assert(simple_landmark_exists(a));
        return *(simple_lms_to_nodes.find(a)->second);
    }
    
    inline LandmarkNode& get_disj_lm_node(const pair<int, int>& a) const {
	// Note: this only works because every proposition appears in only one disj. LM
	assert(!simple_landmark_exists(a));
	assert(disj_lms_to_nodes.find(a) != disj_lms_to_nodes.end());
	return *(disj_lms_to_nodes.find(a)->second);
    }
   
    inline const set<LandmarkNode*>& get_nodes() const {
        return nodes;
    }

    inline const vector<int>& get_operators_including_eff(const pair<int, int>& eff) const {
        return operators_eff_lookup[eff.first][eff.second];
    }

    inline const vector<int>& get_operators_including_pre(const pair<int, int>& pre) const {
        return operators_pre_lookup[pre.first][pre.second];
    }
    inline const Operator& get_operator_for_lookup_index(int op_no) const {
	const Operator& op = (op_no < g_operators.size()) ? 
	    g_operators[op_no] : g_axioms[op_no - g_operators.size()];
	return op;
    }
private:
    bool interferes(const LandmarkNode*, const LandmarkNode*) const;
    bool effect_always_happens(const vector<PrePost>& prepost, 
                               set<pair<int, int> >& eff) const;
    virtual void generate_landmarks() = 0;
    vector<int> empty_pre_operators;
    vector<vector<vector<int> > > operators_eff_lookup;
    vector<vector<vector<int> > > operators_pre_lookup;
    void generate_operators_lookups();
    void approximate_reasonable_orders(bool obedient_orders);
    void mk_acyclic_graph();
    int loop_acyclic_graph(LandmarkNode& lmn, 
                           hash_set<LandmarkNode*, hash_pointer>& acyclic_node_set);

    bool remove_first_weakest_cycle_edge(LandmarkNode* cur, 
                                         list<pair<LandmarkNode*, edge_type> >& path,
                                         list<pair<LandmarkNode*, edge_type> >::iterator it);

protected:
    int landmarks_count;
private:
    int landmarks_cost;
    int calculate_lms_cost() const;
    bool use_external_inconsistencies;
    bool reasonable_orders;

    vector<vector<set<pair<int, int> > > > inconsistent_facts;

protected:

    set<LandmarkNode*> nodes;

    hash_map<pair<int, int>, LandmarkNode*, hash_int_pair> simple_lms_to_nodes;
    hash_map<pair<int, int>, LandmarkNode*, hash_int_pair> disj_lms_to_nodes;

    hash_map<pair<int, int>, Pddl_proposition, hash_int_pair> pddl_propositions;
    map<string, int> pddl_proposition_indeces; //TODO: make this a hash_map

    bool inconsistent(const pair<int,int>& a, const pair<int,int>& b) const;
    void collect_ancestors(hash_set<LandmarkNode*, hash_pointer>& result, LandmarkNode& node, 
                           bool use_reasonable);
    inline bool relaxed_task_solvable(bool level_out,
				      const LandmarkNode* exclude,
				      bool compute_lvl_op = false) const {
        vector<vector<int> > lvl_var;
	vector<hash_map<pair<int, int>, int, hash_int_pair> > lvl_op;
        return relaxed_task_solvable(lvl_var, lvl_op, level_out, exclude, compute_lvl_op);
    }
    bool relaxed_task_solvable(vector<vector<int> >& lvl_var,
			       vector<hash_map<pair<int, int>, int, hash_int_pair> >& lvl_op,
                               bool level_out, 
                               const LandmarkNode* exclude,
			       bool compute_lvl_op = false) const;

    LandmarkNode& landmark_add_simple(const pair<int, int>& lm); 
    LandmarkNode& landmark_add_disjunctive(const set<pair<int, int> >& lm); 
    void edge_add(LandmarkNode& from, LandmarkNode& to, 
                  edge_type type);

};

#endif
