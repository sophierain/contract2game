from __future__ import annotations

from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import Dict, List




# --- top level classes ---

@dataclass
class Act:
    store: Storage
    contracts: List[Contract]



@dataclass
class Contract:
    name: str
    constructor: Constructor
    behaviors: List[Behavior]

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






# --- Interface ---
@dataclass
class Interface:
    name: str
    args: List[Decl]

@dataclass
class Decl:
    name: str
    type: AbiType






# --- Slot Types ---
class SlotType(metaclass=ABCMeta):
    """base class for storage variables"""

# --- Mapping Types ---
@dataclass
class MappingType(SlotType):
    argsType: List[ValueType]
    resultType: ValueType


class ValueType(SlotType, metaclass=ABCMeta):
    """base class for storage base variables"""

"""A description of the shape of global storage"""
Storage = Dict[str, Dict[str, SlotType]]


@dataclass
class ContractType(ValueType):
    contract: str

# --- Abi Types ---

@dataclass
class AbiType(ValueType, metaclass=ABCMeta):
    """base class for solidity abi types"""

@dataclass
class AbiUIntType(AbiType):
    size: int

@dataclass
class AbiIntType(AbiType):
    size: int

@dataclass
class AbiAddressType(AbiType):
    """address type"""

@dataclass
class AbiBoolType(AbiType):
    """bool type"""

@dataclass
class AbiBytesType(AbiType):
    size: int

@dataclass
class AbiBytesDynamicType(AbiType):
    """dynamic bytes type"""

@dataclass
class AbiStringType(AbiType):
    """string type"""

@dataclass
class AbiArrayDynamicType(AbiType):
    arraytype: AbiType

@dataclass
class AbiArrayType(AbiType):
    size: int
    arraytype: AbiType

@dataclass
class AbiTupleType(AbiType):
    tuple: List[AbiType]

@dataclass
class AbiFunctionType(AbiType):
    """function type"""






# --- expressions ---

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

@dataclass
class Eq(BoolExp):
    left: Exp
    right: Exp

@dataclass
class Neq(BoolExp):
    left: Exp
    right: Exp

@dataclass
class InRange(BoolExp):
    expr: IntExp
    abitype: AbiType
    # only allow (int, uint, address) 

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

@dataclass
class Pow(IntExp):
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




    
# --- environment Variables ---

@dataclass  
class EnvVarInt(IntExp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str

@dataclass  
class EnvVarBool(BoolExp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str

@dataclass    
class StorageItem(Exp): # should it also be either bool or int?
    """This is TItem in TimeAgnostic.hs"""
    loc: StorageLoc
    time: Timing





# --- Storage Location ---

class StorageLoc(metaclass=ABCMeta):
    """A reference to an item in storage"""

@dataclass
class VarLoc(StorageLoc):
    """The base variable reference type
       This can either be a value type, or the base of a longer chain of e.g. MappingLoc / ContractLoc expressions
    """ 
    # the contract in which this storage location resides
    contract: str
    # the name of the storage location
    name: str

@dataclass    
class MappingLoc(StorageLoc):
    """A fully applied lookup in a (potentially nested) mapping
       e.g. m[4][3] 
    """
    # the location in storage that holds the mapping (e.g. the m in m[4][3])
    loc: StorageLoc
    # the arguments to the mapping that give us an actual location in storage (e.g. the [4][3] in m[4][3])
    args: List[Exp]

@dataclass    
class ContractLoc(StorageLoc):
    """A reference to a field on a contract that is held in storage
       e.g. c.x.y[3]
    """
    # the location in storage that holds the pointer to the contract (e.g. the c in c.x)
    loc: StorageLoc
    # the name of the contract that the field belongs to (e.g. the type of c in c.x)
    contract: str
    # the name of the field (e.g. the "x" in c.x)
    field: str


class Timing(metaclass=ABCMeta):
    """Is the storage varaible refering to the pre or post state"""

@dataclass
class Pre(Timing):
    """Prestate"""

@dataclass
class Post(Timing):
    """Poststate"""

