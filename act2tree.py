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
from ast2smt import *
from sys import argv



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

act_trees = []
for considered_contract in act.find_maincontract():
       act_trees.append(contract2tree(considered_contract, act.store, extra_constraints))


for tree in act_trees:
      tree.structure()


