from __future__ import annotations

from abc import ABCMeta, abstractmethod
import itertools
import json

from typing import Any, Dict, Iterable, List, Union
import z3
from auxfunz3 import Boolean
from constants import CONSTRAINT_FUNS
from utility import Utility


def load_constraint(source: Union(dict, str))-> Union(Boolean, Utility):
        if isinstance(source, str):
            return Utility.from_name(source, True)

        else:
            list_of_expressions = []
            print(source)
            if "args" in source.keys():
                for expr in source["args"]:#how does the pre thing work there
                    list_of_expressions.append(load_constraint(expr))

                return apply_symbol(list_of_expressions, source["symbol"])
            elif "Pre" in source.keys():
                return load_constraint(source["Pre"]["item"])
            elif "Post" in source.keys():
                return load_constraint(source["Post"]["item"])

def apply_symbol(list_of_expressions: List, symbol: str)-> Union(Boolean, Utility):
        if symbol == "+":
            return list_of_expressions[0] + list_of_expressions[1]
        elif symbol == "-":
            return list_of_expressions[0] - list_of_expressions[1]
        elif symbol == "*":
            return list_of_expressions[0] * list_of_expressions[1] #ignores double infinitesimals
        elif symbol == "/":
            return list_of_expressions[0] / list_of_expressions[1] #ignores double infinitesimals
        elif symbol == "^":
            return list_of_expressions[0] ** list_of_expressions[1] #ignores double infinitesimals, only real exponents allowed

        # elif symbol == "litint":
        #     return list_of_expressions[0] 
        # elif symbol == "intmin": 
        #     return -2 ** (list_of_expressions[0] -1)
        # elif symbol == "intmax":
        #     return 2 ** (list_of_expressions[0] -1) -1
        # elif symbol == "uintmin":
        #     return 0
        # elif symbol == "uintmax":
        #     return 2 ** list_of_expressions[0] -1
        elif symbol == "inrange": #arity 2; type and value
            pass #format issue if expression is not a variable of numeric value
        # elif symbol == "intenv":
        #     pass 
        elif symbol == "ite":
            to_be_conjoint = tuple(z3.Implies(list_of_expressions[0],list_of_expressions[1]), z3.Implies(z3.Not(list_of_expressions[0]),list_of_expressions[2]))
            return z3.And(*to_be_conjoint)


        elif symbol == "and":
            return z3.And(*list_of_expressions)
        elif symbol == "or":
            return z3.Or(*list_of_expressions)
        elif symbol == "<":
            return list_of_expressions[0] < list_of_expressions[1]
        elif symbol == ">":
            return list_of_expressions[0] > list_of_expressions[1]
        elif symbol == "=>":
            return z3.Implies(list_of_expressions[0],list_of_expressions[1])
        elif symbol == "=/=":
            return z3.Not(list_of_expressions[0]==list_of_expressions[1])
        elif symbol == "==":
            return list_of_expressions[0]==list_of_expressions[1]
        elif symbol == "<=":
            return list_of_expressions[0] <= list_of_expressions[1]
        elif symbol == ">=":
            return list_of_expressions[0] >= list_of_expressions[1]
        # elif symbol == "LitBool": #???
        #     pass
        elif symbol == "not":
            return z3.Not(list_of_expressions[0])




class Behavior:
    """one function within a contract in a given case"""
    name: str
    case: List[Boolean]
    preConditions: List[Boolean]
    postConditions: List[Boolean]
    returnValue: Any #z3 expression, to be parsed similar to constraints
    returnType: Any
    stateUpdates: List[Any] #how are state updates specified?

    def __init__(self, behavior: Dict[str, Any]):
        #assert(behavior["kind"]=="Behavior")
        self.name = behavior["name"]
        self.case = [
            load_constraint(elem) 
            for elem in behavior["case"]
        ]
        self.preConditions = [
            load_constraint(elem) 
            for elem in behavior["preConditions"]
        ]
        self.postConditions = [
            load_constraint(elem)
            for elem in behavior["postConditions"]
        ]
        
        self.returnValue = load_constraint(behavior["returns"]["expression"])
        self.returnType = eval(behavior["returns"]["sort"])
        

        self.stateUpdates = [self.load_update(elem) for elem in behavior["stateUpdates"]]

    def __repr__(self) -> str:
        return (
            f"name: {self.name}\n"
            f"case: {self.case}\n"
            f"preConditions: {self.preConditions}\n"
            f"postConditions: {self.postConditions}\n"
            f"returnValue: {self.returnValue}\n"
            f"returnType: {self.returnType}\n"
            f"stateUpdates: {self.stateUpdates}\n"
        )

    def load_update(self, update: Dict) -> Any:
        pass




class Constructor:
    initial_storage: List[Any]
    invariants: List[Boolean] 
    preConditions: List[Boolean]
    postConditions: List[Boolean]

    def __init__(self, constructor: Dict[str, Any]):
        assert(constructor["kind"]=="Constructor")
        self.initial_storage = constructor["initial storage"]
        self.invariants = [
            load_constraint(constraint)
            for constraint in constructor["invariants"]
        ]
        self.preConditions = [
            load_constraint(constraint)
            for constraint in constructor["preConditions"]
        ]        
        self.postConditions = [
            load_constraint(constraint)
            for constraint in constructor["postConditions"]
        ]

    def __repr__(self) -> str:
        return (
            f"initial_storage: {self.initial_storage}\n"
            f"invariants: {self.invariants}\n"
            f"preConditions: {self.preConditions}\n"
            f"postConditions: {self.postConditions}\n"
        )



class Contract:
    """input data"""
    behaviors: List[Behavior]
    constructor: Constructor

    def __init__(self, contract: Dict[str, Any]):
        assert(contract["kind"]=="Contract")
        self.constructor = Constructor(contract["constructor"])
        self.behaviors = [Behavior(elem) for elem in contract["behaviors"]]

    def __repr__(self) -> str:
        return (
            f"behaviors:\n {self.behaviors}\n" 
            f"constructor:\n {self.constructor}\n"
        )
