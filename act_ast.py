from __future__ import annotations

from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import Dict, List, Union, Generator




# --- top level classes ---

@dataclass
class Act:
    store: Storage
    contracts: List[Contract]

    def find_maincontract(self)-> Generator[Contract, None, None]:
        not_main = []
        for key, value in self.store.items():
            for nested_key, nested_value in value.items():
                if isinstance(nested_value, ContractType):
                    not_main.append(nested_value.contract)
        for c in self.contracts: 
            if c.name not in not_main:
                yield c

@dataclass
class Contract:
    name: str
    constructor: Constructor
    behaviors: List[Behavior]

@dataclass
class Constructor:
    interface: Interface
    initial_storage: List[Exp]
    preConditions: List[Exp]
    postConditions: List[Exp]
    invariants: List[Exp]

@dataclass
class Behavior:
    """one function within a contract in a given case"""
    name: str
    interface: Interface
    caseConditions: List[Exp]
    preConditions: List[Exp]
    postConditions: List[Exp]
    returnValue: Exp 
    stateUpdates: List[Exp] #equality constraints e.g. update






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

"""A description of the shape of global storage"""
Storage = Dict[str, Dict[str, SlotType]]

# --- Mapping Types ---
@dataclass
class MappingType(SlotType):
    argsType: List[ValueType] 
    resultType: ValueType 


class ValueType(SlotType, metaclass=ABCMeta):
    """base class for storage base variables"""




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
    type: ActType

class ActType(metaclass=ABCMeta):
    """Base class for act types"""

@dataclass
class ActBool(ActType):
    """"act bool type"""

@dataclass
class ActInt(ActType):
    """act int type"""






@dataclass
class Lit(Exp):
    value: Union[bool, int]
    type: ActType

@dataclass
class Var(Exp):
    name: str
    type: ActType

@dataclass
class And(Exp):
    """conjunction of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Or(Exp):
    """disjunction of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Not(Exp):
    """Negation of a boolean expression"""
    value: Exp
    type: ActType = ActBool()

@dataclass
class Implies(Exp):
    """implication of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class ITE(Exp):
    """description"""
    condition: Exp
    left: Exp
    right: Exp
    type: ActType

@dataclass
class Eq(Exp):
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Neq(Exp):
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class InRange(Exp):
    expr: Exp
    abitype: AbiType # only allow (int, uint, address) 
    type: ActType = ActBool()
    

# arithmetic
@dataclass
class Add(Exp):
    """addition of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

@dataclass 
class Sub(Exp):
    """subtraction of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

@dataclass
class Mul(Exp):
    """multiplication of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

@dataclass
class Div(Exp):
    """division of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

@dataclass
class Pow(Exp):
    """division of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()


# relations 
@dataclass
class Lt(Exp):
    """less than comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Le(Exp):
    """less than or equal comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Gt(Exp):
    """greater than comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

@dataclass
class Ge(Exp):
    """greater than or equal comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()



    
# --- environment Variables ---

@dataclass  
class EnvVar(Exp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str
    type: ActType

@dataclass    
class StorageItem(Exp): 
    """This is TItem in TimeAgnostic.hs"""
    loc: StorageLoc
    time: Timing
    type: ActType




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

