#! /usr/bin/env python2.4
# -*- coding: latin-1 -*-

#######################################################################
#
# Author: Malte Helmert (helmert@informatik.uni-freiburg.de)
# (C) Copyright 2003-2004 Malte Helmert
# Modified by: Gabi Roeger and Silvia Richter (silvia.richter@nicta.com.au)
# (C) Copyright 2008: Gabi Roeger and NICTA
#
# This file is part of LAMA.
#
# LAMA is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 3
# of the license, or (at your option) any later version.
#
# LAMA is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, see <http://www.gnu.org/licenses/>.
#
#######################################################################

import itertools

import normalize
import pddl
import pddl.conditions # for type-checking in translate_facts()
import pddl.f_expression # for type-checking in translate_facts()

class PrologProgram:
  def __init__(self):
    self.facts = []
    self.rules = []
    self.objects = set()
    def predicate_name_generator():
      for count in itertools.count():
        yield "p$%d" % count
    self.new_name = predicate_name_generator()
  def add_fact(self, atom):
    self.facts.append(Fact(atom))
    self.objects |= set(atom.args)
  def add_rule(self, rule):
    self.rules.append(rule)
  def dump(self):
    for fact in self.facts:
      print fact
    for rule in self.rules:
      print getattr(rule, "type", "none"), rule
  def normalize(self):
    # Normalized prolog programs have the following properties:
    # 1. Each variable that occurs in the effect of a rule also occurs in its
    #    condition. 
    # 2. The variables that appear in each effect or condition are distinct.
    # 3. There are no rules with empty condition.
    self.remove_free_effect_variables()
    self.split_duplicate_arguments()
    self.convert_trivial_rules()
  def split_rules(self):
    import split_rules
    # Splits rules whose conditions can be partitioned in such a way that
    # the parts have disjoint variable sets, then split n-ary joins into
    # a number of binary joins, introducing new pseudo-predicates for the
    # intermediate values.
    new_rules = []
    for rule in self.rules:
      new_rules += split_rules.split_rule(rule, self.new_name)
    self.rules = new_rules
  def remove_free_effect_variables(self):
    """Remove free effect variables like the variable Y in the rule
    p(X, Y) :- q(X). This is done by introducing a new predicate
    @object, setting it true for all objects, and translating the above
    rule to p(X, Y) :- q(X), @object(Y).
    After calling this, no new objects should be introduced!"""

    # Note: This should never be necessary for typed domains.
    # Leaving it in at the moment regardless.
    must_add_predicate = False
    for rule in self.rules:
      eff_vars = get_variables([rule.effect])
      cond_vars = get_variables(rule.conditions)
      if not eff_vars.issubset(cond_vars):
        must_add_predicate = True
        eff_vars -= cond_vars
        for var in eff_vars:
          rule.add_condition(pddl.Atom("@object", [var]))
    if must_add_predicate:
      print "Unbound effect variables: Adding @object predicate."
      self.facts += [Fact(pddl.Atom("@object", [obj])) for obj in self.objects]
  def split_duplicate_arguments(self):
    """Make sure that no variable occurs twice within the same symbolic fact,
    like the variable X does in p(X, Y, X). This is done by renaming the second
    and following occurrences of the variable and adding equality conditions.
    For example p(X, Y, X) is translated to p(X, Y, X@0) with the additional
    condition =(X, X@0); the equality predicate must be appropriately instantiated
    somewhere else."""
    printed_message = False
    for rule in self.rules:
      if rule.rename_duplicate_variables() and not printed_message:
        print "Duplicate arguments: Adding equality conditions."
        printed_message = True
  def convert_trivial_rules(self):
    """Convert rules with an empty condition into facts.
    This must be called after bounding rule effects, so that rules with an
    empty condition must necessarily have a variable-free effect.
    Variable-free effects are the only ones for which a distinction between
    ground and symbolic atoms is not necessary."""
    must_delete_rules = []
    for i, rule in enumerate(self.rules):
      if not rule.conditions:
        assert not get_variables([rule.effect])
        self.add_fact(pddl.Atom(rule.effect.predicate, rule.effect.args))
        must_delete_rules.append(i)
    if must_delete_rules:
      print "Trivial rules: Converted to facts."
      for rule_no in must_delete_rules[::-1]:
        del self.rules[rule_no]
    
def get_variables(symbolic_atoms):
  variables = set()
  for sym_atom in symbolic_atoms:
    variables |= set([arg for arg in sym_atom.args if arg[0] == "?"])
  return variables

class Fact:
  def __init__(self, atom):
    self.atom = atom
  def __str__(self):
    return "%s." % self.atom

class Rule:
  def __init__(self, conditions, effect):
    self.conditions = conditions
    self.effect = effect
  def add_condition(self, condition):
    self.conditions.append(condition)
  def get_variables(self):
    return get_variables(self.conditions + [self.effect])
  def _rename_duplicate_variables(self, atom, new_conditions):
    used_variables = set()
    for i, var_name in enumerate(atom.args):
      if var_name[0] == "?":
        if var_name in used_variables:
          new_var_name = "%s@%d" % (var_name, len(new_conditions))
          atom.args[i] = new_var_name
          new_conditions.append(pddl.Atom("=", [var_name, new_var_name]))
        else:
          used_variables.add(var_name)
  def rename_duplicate_variables(self):
    new_conditions = []
    self._rename_duplicate_variables(self.effect, new_conditions)
    for condition in self.conditions:
      self._rename_duplicate_variables(condition, new_conditions)
    self.conditions += new_conditions
    return bool(new_conditions)
  def __str__(self):
    cond_str = ", ".join(map(str, self.conditions))
    return "%s :- %s." % (self.effect, cond_str)

def translate_typed_object(prog, obj, type_dict):
  supertypes = type_dict[obj.type].supertype_names
  for type_name in [obj.type] + supertypes:
    prog.add_fact(pddl.Atom(type_name, [obj.name]))

def translate_facts(prog, task):
  type_dict = dict((type.name, type) for type in task.types)
  for obj in task.objects:
    translate_typed_object(prog, obj, type_dict)
  for fact in task.init:
    assert isinstance(fact, pddl.conditions.Atom) or isinstance(fact, pddl.f_expression.Assign)
    if isinstance(fact, pddl.conditions.Atom):
      prog.add_fact(fact)

def translate(task):
  normalize.normalize(task)
  prog = PrologProgram()
  translate_facts(prog, task)
  for conditions, effect in normalize.build_exploration_rules(task):
    prog.add_rule(Rule(conditions, effect))
  prog.normalize()
  prog.split_rules()
  return prog

def test_normalization():
  prog = PrologProgram()
  prog.add_fact(pddl.Atom("at", ["foo", "bar"]))
  prog.add_fact(pddl.Atom("truck", ["bollerwagen"]))
  prog.add_fact(pddl.Atom("truck", ["segway"]))
  prog.add_rule(Rule([pddl.Atom("truck", ["?X"])], pddl.Atom("at", ["?X", "?Y"])))
  prog.add_rule(Rule([pddl.Atom("truck", ["X"]), pddl.Atom("location", ["?Y"])],
                pddl.Atom("at", ["?X", "?Y"])))
  prog.add_rule(Rule([pddl.Atom("truck", ["?X"]), pddl.Atom("location", ["?Y"])],
                pddl.Atom("at", ["?X", "?X"])))
  prog.add_rule(Rule([pddl.Atom("p", ["?Y", "?Z", "?Y", "?Z"])],
                pddl.Atom("q", ["?Y", "?Y"])))
  prog.add_rule(Rule([], pddl.Atom("foo", [])))
  prog.add_rule(Rule([], pddl.Atom("bar", ["X"])))
  prog.normalize()
  prog.dump()

if __name__ == "__main__":
  # test_normalization()

  task = pddl.open()
  prog = translate(task)
  prog.dump()
