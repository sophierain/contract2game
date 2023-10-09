from __future__ import annotations

from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
import itertools
import json

from typing import Any, Dict, Iterable, List, Union
import z3
from auxfunz3 import Boolean
from constants import CONSTRAINT_FUNS
from utility import Utility



class Exp(metaclass=ABCMeta):
    """base class for expressions"""


class IntExp(Exp, metaclass=ABCMeta):
    """integer expressions"""

class BoolExp(Exp, metaclass=ABCMeta):
    """boolean expressions"""

@dataclass
class LitBool(BoolExp):
    value: bool


@dataclass
class And(BoolExp):
    """conjunction of two boolean expressions"""
    left: BoolExp
    right: BoolExp

@dataclass
class Or(BoolExp):
    """disjunction of two boolean expressions"""
    left: BoolExp
    right: BoolExp

class Not(BoolExp):
    """Negation of a boolean expression"""
    value: BoolExp

   
    def __init__(self, value: BoolExp):
        """not value"""
        self.value = value

    def __repr__(self):
        return f"Not({self.value})"


class Implies(BoolExp):
    """implication of two boolean expressions"""
    left: BoolExp
    right: BoolExp

   
    def __init__(self, left: BoolExp, right: BoolExp):
        """left or right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Implies({self.left}, {self.right})"

class Eq(BoolExp):
    left: Exp
    right: Exp

    def __init__(self, left: BoolExp, right: BoolExp):
        self.left = left
        self.right = right

    def __init__(self, left: IntExp, right: IntExp):
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Eq({self.left}, {self.right})" 

# arithmetic
class LitInt(IntExp):
    value: int

    def __init__(self, value: int):
        """just an integer"""
        self.value = value
 

    def __repr__(self):
        return f"LitInt({self.value})"

class Add(IntExp):
    """addition of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left plus right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Add({self.left}, {self.right})"
    
class Sub(IntExp):
    """subtraction of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left minus right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Sub({self.left}, {self.right})"

class Mul(IntExp):
    """multiplication of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left times right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Mul({self.left}, {self.right})"


class Div(IntExp):
    """division of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left divided by right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Div({self.left}, {self.right})"


# relations of IntBool
class Lt(BoolExp):
    """less than comparison of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left < right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Lt({self.left}, {self.right})"

class Le(BoolExp):
    """less than or equal comparison of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left <= right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Le({self.left}, {self.right})"

class Gt(BoolExp):
    """greater than comparison of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left >= right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Gt({self.left}, {self.right})"

class Ge(BoolExp):
    """greater than or equal comparison of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left >= right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Ge({self.left}, {self.right})"


class Neq(BoolExp):
    """inequality of two integer expressions"""
    left: IntExp
    right: IntExp

   
    def __init__(self, left: IntExp, right: IntExp):
        """left != right"""
        self.left = left
        self.right = right

    def __repr__(self):
        return f"Neq({self.left}, {self.right})"
    

# mappings and stuff
class ActTy(metaclass=ABCMeta):
    """base class for act types"""

class IntTy(ActTy):
    """Integers"""

    def __repr__(self) -> str:
        return "IntTy"

class BoolTy(ActTy):
    """Booleans"""

    def __repr__(self) -> str:
        return "BoolTy"

class Decl:
    name: str
    ty: ActTy

    def __init__(self, name: str, ty: ActTy):
        self.name = name
        self.ty = ty

    def __repr__(self) -> str:
        return f"Decl({self.name}, {self.ty})"

class Interface:
    name: str
    args: List[Decl]

    def __init__(self, name: str, args: List[Decl]):
        self.name = name
        self.args = args
    
    def __repr__(self) -> str:
        return f"Interface({self.name}, {self.args})"
    
# --- Variables ---

class Var(Exp):
    """A reference to a calldata variable"""
    name: str

    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return f"Var({self.name})"
    
class EnvVar(IntExp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str

    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return f"EnvVar({self.name})"
    
class StorageItem(Exp):
    """This is TItem in TimeAgnostic.hs"""
    item: StorageLoc
    time: Timing

    def __init__(self, item: StorageLoc, time: Timing):
        self.item = item
        self.time = time

    def __repr__(self) -> str:
        return f"StorageVar({self.item}, {self.time})"


# --- Storage ---

class Timing(metaclass=ABCMeta):
    """Is the storage varaible refering to the pre or post state"""

class Pre(Timing):
    """Prestate"""

class Post(Timing):
    """Poststate"""

    
class StorageLoc(metaclass=ABCMeta):
    """A reference to an item in storage"""


class VarLoc(StorageLoc):
    """The base variable reference type
       This can either be a value type, or the base of a longer chain of e.g. MappingLoc / ContractLoc expressions
    """
    contract: str
    name: str

    def __init__(self, contract: str, name: str):
        self.contract = contract
        self.name = name

    def __repr__(self) -> str:
        return f"VarLoc({self.contract}, {self.name})"
    
class MappingLoc(StorageLoc):
    """A fully applied lookup in a (potentially nested) mapping
       e.g. m[4][3] 
    """
    loc: StorageLoc
    args: List[Exp]

    def __init__(self, loc: str, args: List[Exp]):
        self.loc = loc
        self.args = args

    def __repr__(self) -> str:
        return f"MappingLoc({self.loc}, {self.args})"
    
class ContractLoc(StorageLoc):
    """A reference to a field on a contract that is held in storage
       e.g. c.x.y[3]
    """
    loc: StorageLoc
    contract: str
    name: str

    def __init__(self, loc: StorageLoc, contract: str, name: str):
        self.loc = loc
        self.contract = contract
        self.name = name

    def __repr__(self) -> str:
        return f"ContractLoc({self.loc}, {self.contract}, {self.name})"

class Constructor:
    initial_storage: List[BoolExp]
    preConditions: List[BoolExp]
    postConditions: List[BoolExp]
    invariants: List[BoolExp]

class Behavior:
    """one function within a contract in a given case"""
    name: str
    interface: Interface
    caseConditions: List[BoolExp]
    preConditions: List[BoolExp]
    postConditions: List[BoolExp]
    returnValue: Exp 
    stateUpdates: List[BoolExp] #equality constraints e.g. update

class Storage:
    """A description of the shape of global storage"""
    store: Dict[str, Dict[str, AbiType]]

class Contract:
    constructor: Constructor
    behaviors: List[Behavior]

class Act:
    store: store
    contracts: List[Contract]


class AbiType:
    """TODO: fill me out with the solidity abi types"""