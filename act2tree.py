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


from typing import Any, Dict, Iterable, List, Union
import z3

#path = input("path to json respresenation of act specification\n")
#path = "act_examples/smoke/smoke.act.typed.json"
#path = "act_examples/token/transfer.act.typed.json"
from sys import argv
path = argv[1]

obj = json.load(open(path))




act = parse_act_json(obj)



# considered_contract = Contract(contracts[0])

# print(considered_contract)

x=LitBool(True)
y=And(x, x)

z = And(LitBool(True), LitBool(True))
    
print(z)