#######################################################################
#
# Author: Gabi Roeger
# Modified by: Silvia Richter (silvia.richter@nicta.com.au)
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

import string
import conditions

def parse_expression(exp):
    if isinstance(exp, list):
        alist = exp
        operator_or_functionsymbol = alist[0]
        if operator_or_functionsymbol in ("+","/","*","-"):
            args = [parse_expression(arg) for arg in alist[1:]]
            operator = operator_or_functionsymbol
        else:
            return PrimitiveNumericExpression(operator_or_functionsymbol,
                                              [conditions.parse_term(arg) for arg in alist[1:]])
    elif exp.replace(".","").isdigit():
        return NumericConstant(string.atof(exp))
    else:
        return PrimitiveNumericExpression(exp,[])

def parse_assignment(alist):
    assert len(alist) == 3
    op = alist[0]
    head = parse_expression(alist[1])
    exp = parse_expression(alist[2])
    if op == "=":
        return Assign(head, exp)
    elif op == "increase":
        return Increase(head, exp)
    else:
        assert False, "Assignment operator not supported."

class FunctionalExpression(object):
    def __init__(self, parts):
        self.parts = tuple(parts)
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        for part in self.parts:
            part.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def instantiate(self, var_mapping, init_facts):
        raise ValueError("Cannot instantiate condition: not normalized")

class NumericConstant(FunctionalExpression):
    parts = ()
    def __init__(self, value):
        self.value = value
    def __eq__(self, other):
        return (self.__class__ == other.__class__ and self.value == other.value)
    def __str__(self):
        return "%s %s" % (self.__class__.__name__, self.value)
    def _dump(self):
        return str(self)
    def instantiate(self, var_mapping, init_facts):
        return self

class PrimitiveNumericExpression(FunctionalExpression):
    parts = ()
    def __init__(self, symbol, args):
        self.symbol = symbol
        self.args = tuple(args)
    def __eq__(self, other):
        if not (self.__class__ == other.__class__ and self.symbol == other.symbol
                and len(self.args) == len(other.args)):
            return False
        else:
            for s,o in zip(self.args, other.args):
                if not s == o:
                    return False
            return True    
    def __str__(self):
        return "%s %s(%s)" % ("PNE", self.symbol, ", ".join(map(str, self.args)))
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        for arg in self.args:
            arg.dump(indent + "  ")
    def _dump(self):
        return str(self)
    def  instantiate(self, var_mapping, init_facts):
        args = [conditions.ObjectTerm(var_mapping.get(arg.name, arg.name)) for arg in self.args]
        pne = PrimitiveNumericExpression(self.symbol, args)
        assert not self.symbol == "total-cost"
        # We know this expression is constant. Substitute it by corresponding 
        # initialization from task.
        for fact in init_facts:
            if isinstance(fact, FunctionAssignment):
                if fact.fluent == pne:
                    return fact.expression
        assert False, "Could not find instantiation for PNE!"

class FunctionAssignment(object):
    def __init__(self, fluent, expression):
        self.fluent = fluent
        self.expression = expression
    def __str__(self):
        return "%s %s %s" % (self.__class__.__name__, self.fluent, self.expression) 
    def dump(self, indent="  "):
        print "%s%s" % (indent, self._dump())
        self.fluent.dump(indent + "  ")
        self.expression.dump(indent + "  ")
    def _dump(self):
        return self.__class__.__name__
    def instantiate(self, var_mapping, init_facts):
        if not (isinstance(self.expression, PrimitiveNumericExpression) or
                isinstance(self.expression, NumericConstant)):
            raise ValueError("Cannot instantiate assignment: not normalized")
        # We know that this assignment is a cost effect of an action (for initial state
        # assignments, "instantiate" is not called). Hence, we know that the fluent is
        # the 0-ary "total-cost" which does not need to be instantiated
        assert self.fluent.symbol == "total-cost"
        fluent = self.fluent
        expression = self.expression.instantiate(var_mapping, init_facts)
        return self.__class__(fluent, expression)

class Assign(FunctionAssignment):
    def __str__(self):
        return "%s := %s" % (self.fluent, self.expression) 

class Increase(FunctionAssignment):
    pass

