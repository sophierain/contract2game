#!/usr/bin/env python3
"""
input: json version of act specification;
       constraints on the initial state
output: a tree of possible function calls
"""
from __future__ import annotations

import json
from act_ast import *
from parse_act import parse_act_json, parse_constraints_json
from state_tree import *
from pest import *
from sys import argv
from case_splitting import *
from collections.abc import Callable

path = argv[1]

obj = json.load(open(path))


if len(argv) > 2:
       path_extra_constraints = argv[2]
       extra_obj = json.load(open(path_extra_constraints))
       extra_constraints = parse_constraints_json(extra_obj)
else: 
       extra_constraints = []

# parse json into an Act instance
act = parse_act_json(obj)

act.to_cnf()

players = [Player("A", []), Player("B", [])]

act_trees = []
for considered_contract in act.find_maincontract():
       act_trees.append(contract2pest(considered_contract, extra_constraints, act.store, players))

# called on each leaf node. takes a history of called methods and the state tracker at that leaf
# returns a utility map
UtilityFn = Callable[[List[Tuple[str,Player]], Tracker], Dict[Player, Exp]]

def compute_utilities(UtilityFn, Tree):
    pass



# print player enhanced state trees (their structure)
for tree in act_trees:
       tree.structure()
       print("\n")

# apply case splitting algorithm to all trees
for tree in act_trees:
       _ = case_split(tree, [], tree, players)
       print("\n")
       print("case splitting done")
       print("\n")
       tree.structure()
       print("\n")

# apply player pruning to all trees
for tree in act_trees:
       player_pruning(tree, [], players)
       print("\n")
       print("player pruning done")
       print("\n")
       tree.structure()
       print("\n")