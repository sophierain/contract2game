#!/usr/bin/env python3
"""
input: json version of act specification;
       constraints on the initial state
output: a tree of possible function calls
"""
from __future__ import annotations

from abc import ABCMeta, abstractmethod
import itertools
import json
from act_ast import Contract, LitBool, And
from parse_act import parse_act_json
from ast2smt import *
from smt2tree import *


from typing import Any, Dict, Iterable, List, Union
import z3

#path = input("path to json respresenation of act specification\n")
#path = "act_examples/smoke/smoke.act.typed.json"
#path = "act_examples/token/transfer.act.typed.json"
from sys import argv
path = argv[1]

obj = json.load(open(path))

# parse json into an Act instance
act = parse_act_json(obj)

act_trees = []
for considered_contract in act.find_maincontract():
       act_trees.append(contract2tree(considered_contract, act.storage))





# print(considered_contract)

x=LitBool(True)
y=And(x, x)

z = And(LitBool(True), LitBool(True))
    
print(z)