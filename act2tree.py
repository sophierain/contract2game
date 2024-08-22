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
from postprocessing import *

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

#############################################################################################################################
# USER DEFINED START
players = [Player("A", []), Player("B", [])]

# utility_fct: UtilityFn
def utility_fct(arg1: List[Tuple[str,Player]], arg2: Tracker) -> Dict[str, Exp]:

       p0: Exp = Lit(10, ActInt())
       p1: Exp = Lit(0, ActInt())
       utility = {players[0].name: p0 , players[1].name: p1}

       return utility

honest_histories: List[List[str]] = [["ignore(B)", "ignore(A)"]]

# USER DEFINED END
#############################################################################################################################


act_trees = []
for considered_contract in act.find_maincontract():
       act_trees.append(contract2pest(considered_contract, extra_constraints, act.store, players))


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

# TODO: enable user to provide honest history and utility function here

# post-processing: compute utilities, collect constraints, generate json game tree
assert len(path.split(".json")) > 0, "unexpected file extension"  
output_name : str = path.split(".json")[0]
i : int = 1
for tree in act_trees:
       store_json(tree, utility_fct, players, honest_histories, output_name, str(i))
       i = i + 1