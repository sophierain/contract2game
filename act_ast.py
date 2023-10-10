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
class VarBool(BoolExp):
    name: str

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

@dataclass
class Not(BoolExp):
    """Negation of a boolean expression"""
    value: BoolExp

@dataclass
class Implies(BoolExp):
    """implication of two boolean expressions"""
    left: BoolExp
    right: BoolExp

@dataclass
class ITEInt(IntExp):
    condition: BoolExp
    left: IntExp
    right: IntExp

@dataclass
class ITEBool(BoolExp):
    condition: BoolExp
    left: BoolExp
    right: BoolExp

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
@dataclass
class LitInt(IntExp):
    value: int

@dataclass
class VarInt(IntExp):
    name: str

@dataclass
class Add(IntExp):
    """addition of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass 
class Sub(IntExp):
    """subtraction of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Mul(IntExp):
    """multiplication of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Div(IntExp):
    """division of two integer expressions"""
    left: IntExp
    right: IntExp


# relations of IntBool
@dataclass
class Lt(BoolExp):
    """less than comparison of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Le(BoolExp):
    """less than or equal comparison of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Gt(BoolExp):
    """greater than comparison of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Ge(BoolExp):
    """greater than or equal comparison of two integer expressions"""
    left: IntExp
    right: IntExp

@dataclass
class Neq(BoolExp):
    """inequality of two integer expressions"""
    left: IntExp
    right: IntExp

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

@dataclass
class Decl:
    name: str
    ty: ActTy

@dataclass
class Interface:
    name: str
    args: List[Decl]

    
# --- Variables ---

# @dataclass
# class Var(Exp):
#     """A reference to a calldata variable"""
#     name: str

@dataclass  
class EnvVarInt(IntExp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str

@dataclass  
class EnvVarBool(BoolExp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str

@dataclass    
class StorageItem(Exp):
    """This is TItem in TimeAgnostic.hs"""
    item: StorageLoc
    time: Timing


# --- Storage ---

class Timing(metaclass=ABCMeta):
    """Is the storage varaible refering to the pre or post state"""

@dataclass
class Pre(Timing):
    """Prestate"""

@dataclass
class Post(Timing):
    """Poststate"""

class StorageLoc(metaclass=ABCMeta):
    """A reference to an item in storage"""

@dataclass
class VarLoc(StorageLoc):
    """The base variable reference type
       This can either be a value type, or the base of a longer chain of e.g. MappingLoc / ContractLoc expressions
    """
    contract: str
    name: str

@dataclass    
class MappingLoc(StorageLoc):
    """A fully applied lookup in a (potentially nested) mapping
       e.g. m[4][3] 
    """
    loc: StorageLoc
    args: List[Exp]

@dataclass    
class ContractLoc(StorageLoc):
    """A reference to a field on a contract that is held in storage
       e.g. c.x.y[3]
    """
    loc: StorageLoc
    contract: str
    name: str

@dataclass
class Constructor:
    interface: Interface
    initial_storage: List[BoolExp]
    preConditions: List[BoolExp]
    postConditions: List[BoolExp]
    invariants: List[BoolExp]

@dataclass
class Behavior:
    """one function within a contract in a given case"""
    name: str
    interface: Interface
    caseConditions: List[BoolExp]
    preConditions: List[BoolExp]
    postConditions: List[BoolExp]
    returnValue: Exp 
    stateUpdates: List[BoolExp] #equality constraints e.g. update

@dataclass
class Storage:
    """A description of the shape of global storage"""
    store: Dict[str, Dict[str, AbiType]]

@dataclass
class Contract:
    name: str
    constructor: Constructor
    behaviors: List[Behavior]

@dataclass
class Act:
    store: Storage
    contracts: List[Contract]

@dataclass
class AbiType:
    """TODO: fill me out with the solidity abi types"""