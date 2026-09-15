#!/usr/bin/env python3
from itertools import chain, combinations
import collections
import sys

"""
Script to analyse useful permission combinations according to given constraints.
Outputs the number of useful combinations on stderr and a dot graph
representation on stdout.
"""

# We support a tiny constraint language of boolean expressions that are
# evaluated with respect to a context consisting of a set of permissions that
# are true. We then evaluate the constraints for all subsets of the permissions
# keeping only those subsets that are consistent with all the constraints.
class Expr:
    pass

class Id(Expr):
    def __init__(self, name):
        self.name = name
    def eval(self, context):
        # A name is true if it is in the context, otherwise false
        return self.name in context

class Not(Expr):
    def __init__(self, e):
        self.e = e
    def eval(self, context):
        return not self.e.eval(context)

class And(Expr):
    def __init__(self, l, r):
        self.l = l
        self.r = r
    def eval(self, context):
        return self.l.eval(context) and self.r.eval(context)

class Or(Expr):
    def __init__(self, l, r):
        self.l = l
        self.r = r
    def eval(self, context):
        return self.l.eval(context) or self.r.eval(context)

class Implies(Expr):
    def __init__(self, l, r):
        self.l = l
        self.r = r
    def eval(self, context):
        return (not self.l.eval(context)) or self.r.eval(context)

"""
Builder class that allows us to construct constraints using operator
overloading. Supports ~ (not), &, |, >> (implies)
"""
class Builder:
    def __init__(self, val):
        self.val = val
    def __invert__(self):
        return Builder(Not(self.val))
    def __and__(self, other):
        return Builder(And(self.val, other.val))
    def __or__(self,other):
        return Builder(Or(self.val, other.val))
    def __rshift__(self, other):
        return Builder(Implies(self.val, other.val))

# The set of permissions
perms=set("""\
EX
SR
LG
LM
SL
MC
SD
LD
SE
US
U0
""".split())
# Create a python variable with the name of each permission containing a
# Builder identifying that permission.
for perm in perms:
    locals()[perm]=Builder(Id(perm))

constraints = [
# Read / write cap without data is not useful
    MC >> (LD | SD),
# Access system regs only makes sense on exe caps
    SR >> EX,
# Load global requires load cap
    LG >> (MC & LD),
# Load mutable requires load cap
    LM >> (MC & LD),
# Store local requires store cap
    SL >> (MC & SD),
# We want executable caps to have load cap
    EX >> (MC & LD),
# We do not permit writable and executable caps
    ~(EX & SD),
# Sealing and data permissions are mutually exclusive
    ~((SE | US | U0) & (SD | LD)),
# We originally forbade write-only but had some spare encodings so were able
# to reintroduce it. As a compromise to get us down to 32 combinations and
# a 5-bit encoding we eliminate write-only store-local.
    # SD >> LD, # forbid write-only?
    SL >> LD,   # eliminating store-local write-only gets us down to 32 combinations
]

def powerset(iterable):
    """list(powerset([1,2,3])) --> [(), (1,), (2,), (3,), (1,2), (1,3), (2,3), (1,2,3)]
    Example from https://docs.python.org/3/library/itertools.html#itertools-recipes"""
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def filter_expr(ss, e):
    for s in ss:
        if e.eval(s):
            yield s

subsets = powerset(perms)
for constraint in constraints:
    subsets = filter_expr(subsets, constraint.val)

useful_combinations = list(subsets)
sys.stderr.write(f"{len(useful_combinations)} combinations\n")

def comb_to_str(c):
    """Creates a string from a permission combination.
    Used as node names in dot graph."""
    cs = sorted(c)
    return '_'.join(cs) or "0"

# Now we output a graph representation of the useful combinations in dot format.
# To make it pretty we add edges for the subset partial order.

print("digraph {")

# Output the names of nodes in the graph
for x in useful_combinations:
    print(comb_to_str(x))

# Output the edges for the subset relation. This results in many redundant edges
# but fortunately graphviz provides `tred` for computing the transitive
# reduction.
for x in useful_combinations:
    for y in useful_combinations:
        xs = set(x)
        ys = set(y)
        if xs < ys:
            # find the permissions in ys not in xs to use as label
            diff = ys - xs
            x_str=comb_to_str(x)
            y_str=comb_to_str(y)
            print(f"{y_str} -> {x_str} [label=\"{comb_to_str(diff)}\", fontsize=10]")

print("}")
