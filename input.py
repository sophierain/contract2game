from __future__ import annotations

from abc import ABCMeta, abstractmethod
import itertools
import json

from typing import Any, Dict, Iterable, List, Union
import z3
from auxfunz3 import Boolean
from constants import CONSTRAINT_FUNS
from utility import Utility


class Behavior:
    """one function within a contract in a given case"""
    name: str
    case: List[Boolean]
    preConditions: List[Boolean]
    postConditions: List[Boolean]
    returnValue: Any #what return types are valid in act?
    stateUpdates: List[Any] #how are state updates specified?

    def __init__(self, behavior: Dict[str, Any]):
        self.name = behavior["name"]
        self.case = [
            self.load_constraint(elem) 
            for elem in behavior["case"]
        ]
        self.preConditions = [
            self.load_constraint(elem) 
            for elem in behavior["preConditions"]
        ]
        self.postConditions = [
            self.load_constraint(elem)
            for elem in behavior["postConditions"]
        ]

        value = eval(behavior["returns"]["expresssion"])
        sort = eval(behavior["returns"]["sort"])
        self.returnValue = sort(value)

        self.stateUpdates = [elem for elem in behavior["stateUpdates"]]

    def __repr__(self) -> str:
        return (
            f"name: {self.name}\n"
            f"case: {self.case}\n"
            f"preConditions: {self.preConditions}\n"
            f"postConditions: {self.postConditions}\n"
            f"returnValue: {self.returnValue}\n"
            f"stateUpdates: {self.stateUpdates}\n"
        )

    def translate_constraint(self, source: Union(Dict, str)) -> (str, Dict[str, Utility]):
    
        if type(source) == dict:
            assert(source["arity"] == 2)
            left_arg, left_constants = self.translate_constraint(source["args"][0]) 
            right_arg, right_constants = self.translate_constraint(source["args"][1])
            symbol = source["symbol"]
            merged_constants = {key: value for key, value in left_constants.items()}
            merged_constants.update(right_constants)
            return "( " + left_arg + " " + symbol + " " + right_arg + " )", merged_constants
        else:
            # map from names to Utility, used for eval() later
            constant_dict = {
                constant: Utility.from_name(constant, real)
                for constant, real in
                itertools.chain(
                    ((constant, True) for constant in [source])
                )
            }
            return source, constant_dict


    def load_constraint(self, source: Dict) -> Boolean:
        """load a string expression into a Boolean constraint, via `eval()`"""
        name, constants = self.translate_constraint(source)
        return eval(name, CONSTRAINT_FUNS, constants)



class Constructor:
    initial_storage: List[Any]
    invariants: List[Boolean] 
    preConditions: List[Boolean]
    postConditions: List[Boolean]

    def __init__(self, constructor: Dict[str, Any]):
        self.initial_storage = constructor["initial storage"]
        self.invariants = [
            self.load_constraint(constraint)
            for constraint in constructor["invariants"]
        ]
        self.preConditions = [
            self.load_constraint(constraint)
            for constraint in constructor["preConditions"]
        ]        
        self.postConditions = [
            self.load_constraint(constraint)
            for constraint in constructor["postConditions"]
        ]

    def __repr__(self) -> str:
        return (
            f"initial_storage: {self.initial_storage}\n"
            f"invariants: {self.invariants}\n"
            f"preConditions: {self.preConditions}\n"
            f"postConditions: {self.postConditions}\n"
        )

    def translate_constraint(self, source: Union(Dict, str)) -> (str, Dict):
    
        if type(source) == Dict:
            assert(source["arity"] == 2)
            left_arg, left_constants = self.translate_constraint(source["args"][0]) 
            right_arg, right_constants = self.translate_constraint(source["args"][1])
            symbol = source["symbol"]
            merged_constants = {key: value for key, value in left_constants.items()}
            merged_constants.update(right_constants)
            return "( " + left_arg + " " + symbol + " " + right_arg + " )", merged_constants
        else:
            return source, {source: Utility.from_name(source, True)}


    def load_constraint(self, source: Dict) -> Boolean:
        """load a string expression into a Boolean constraint, via `eval()`"""
        name, constants = self.translate_constraint(source)
        return eval(name, CONSTRAINT_FUNS, constants)




class Contract:
    """input data"""
    behaviors: List[Behavior]
    constructor: Constructor

    def __init__(self, contract: Dict[str, Any]):
        self.constructor = Constructor(contract["constructor"])
        self.behavior = [Behavior(elem) for elem in contract["behaviors"]]

    def __repr__(self) -> str:
        return (
            f"behaviors: {self.behaviors}\n" 
            f"constructor: {self.constructor}\n"
        )
