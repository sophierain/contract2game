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

    def to_cnf(self):
        for elem in self.contracts:
            elem.to_cnf()



@dataclass
class Contract:
    name: str
    constructor: Constructor
    behaviors: List[Behavior]

    def to_cnf(self):

        self.constructor.to_cnf()

        for elem in self.behaviors:
            elem.to_cnf()

@dataclass
class Constructor:
    interface: Interface
    initial_storage: List[Exp]
    preConditions: List[Exp]
    postConditions: List[Exp]
    invariants: List[Exp]

    def to_cnf(self):

        cnf_pre = []
        for elem in self.preConditions:
            cnf_pre.extend(to_cnf(elem))

        cnf_post = []
        for elem in self.postConditions:
            cnf_post.extend(to_cnf(elem))

        cnf_inv = []
        for elem in self.invariants:
            cnf_inv.extend(to_cnf(elem)) 

        self.preConditions = cnf_pre
        self.postConditions = cnf_post
        self.invariants = cnf_inv

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

    def to_cnf(self):

        cnf_case = []
        for elem in self.caseConditions:
            cnf_case.extend(to_cnf(elem))

        cnf_pre = []
        for elem in self.preConditions:
            cnf_pre.extend(to_cnf(elem))

        cnf_post = []
        for elem in self.postConditions:
            cnf_post.extend(to_cnf(elem))

        cnf_updates = []
        for elem in self.stateUpdates:
            cnf_updates.extend(to_cnf(elem)) 

        self.caseConditions = cnf_case
        self.preConditions = cnf_pre
        self.postConditions = cnf_post
        self.stateUpdates = cnf_updates


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

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiUIntType):
            return False
        if self.size != other.size:
            return False
        return True

@dataclass
class AbiIntType(AbiType):
    size: int

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiIntType):
            return False
        if self.size != other.size:
            return False
        return True

@dataclass
class AbiAddressType(AbiType):
    """address type"""

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiAddressType):
            return False
        return True

@dataclass
class AbiBoolType(AbiType):
    """bool type"""

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiBoolType):
            return False
        return True

@dataclass
class AbiBytesType(AbiType):
    size: int

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiBytesType):
            return False
        if self.size != other.size:
            return False
        return True

@dataclass
class AbiBytesDynamicType(AbiType):
    """dynamic bytes type"""

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiBytesDynamicType):
            return False
        return True

@dataclass
class AbiStringType(AbiType):
    """string type"""

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiStringType):
            return False
        return True

@dataclass
class AbiArrayDynamicType(AbiType):
    arraytype: AbiType

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiArrayDynamicType):
            return False
        if self.arraytype.is_equiv(other.arraytype):
            return False
        return True

@dataclass
class AbiArrayType(AbiType):
    size: int
    arraytype: AbiType

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiArrayType):
            return False
        if self.size != other.size:
            return False
        if self.arraytype.is_equiv(other.arraytype):
            return False
        return True

@dataclass
class AbiTupleType(AbiType):
    tuple: List[AbiType]

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiTupleType):
            return False
        if len(self.tuple) != len(other.tuple):
            return False
        for i in range(len(self.tuple)):
            if self.tuple[i].is_equiv(other.tuple[i]):
                return False
        return True

@dataclass
class AbiFunctionType(AbiType):
    """function type"""

    def is_equiv(self, other: AbiType):
        if not isinstance(other, AbiFunctionType):
            return False
        return True





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
class ActByteStr(ActType):
    """act bytestring type"""




@dataclass
class Lit(Exp):
    value: Union[bool, int, str]
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Lit):
            return False
        if self.type != other.type:
            return False
        if self.value != other.value:
            return False
        return True

@dataclass
class Var(Exp):
    name: str
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Var):
            return False
        if self.type != other.type:
            return False
        if self.name != other.name:
            return False
        return True

@dataclass
class And(Exp):
    """conjunction of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, And):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Or(Exp):
    """disjunction of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Or):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Not(Exp):
    """Negation of a boolean expression"""
    value: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Not):
            return False
        if self.type != other.type:
            return False
        if not self.value.is_equiv(other.value):
            return False
        return True

@dataclass
class Implies(Exp):
    """implication of two boolean expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Implies):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class ITE(Exp):
    """description"""
    condition: Exp
    left: Exp
    right: Exp
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, ITE):
            return False
        if self.type != other.type:
            return False
        if not self.condition.is_equiv(other.condition):
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Eq(Exp):
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Eq):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Neq(Exp):
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Neq):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True
             
@dataclass
class InRange(Exp):
    expr: Exp
    abitype: AbiType # only allow (int, uint, address, string) 
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, InRange):
            return False
        if self.type != other.type:
            return False
        if not self.expr.is_equiv(other.expr):
            return False
        if not self.abitype.is_equiv(other.abitype):
            return False
        return True
    

# arithmetic
@dataclass
class Add(Exp):
    """addition of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Add):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass 
class Sub(Exp):
    """subtraction of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Sub):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Mul(Exp):
    """multiplication of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Mul):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Div(Exp):
    """division of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Div):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Pow(Exp):
    """division of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActInt()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Pow):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

# relations 
@dataclass
class Lt(Exp):
    """less than comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Lt):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Le(Exp):
    """less than or equal comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Le):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Gt(Exp):
    """greater than comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Gt):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

@dataclass
class Ge(Exp):
    """greater than or equal comparison of two integer expressions"""
    left: Exp
    right: Exp
    type: ActType = ActBool()

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, Ge):
            return False
        if self.type != other.type:
            return False
        if not self.left.is_equiv(other.left):
            return False
        if not self.right.is_equiv(other.right):
            return False
        return True

    
# --- environment Variables ---

@dataclass  
class EnvVar(Exp):
    """A reference to an environment variable (e.g. msg.sender)"""
    name: str
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, EnvVar):
            return False
        if self.type != other.type:
            return False
        if self.name != other.name:
            return False
        return True

@dataclass    
class StorageItem(Exp): 
    """This is TItem in TimeAgnostic.hs"""
    loc: StorageLoc
    time: Timing
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, StorageItem):
            return False
        if self.type != other.type:
            return False
        if self.time != other.time:
            return False
        if not self.loc.is_equiv(other.loc):
            return False
        return True


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

    def is_equiv(self, other: StorageLoc) -> bool:
        if not isinstance(other, VarLoc):
            return False
        if self.contract != other.contract:
            return False
        if self.name != other.name:
            return False
        return True

@dataclass    
class MappingLoc(StorageLoc):
    """A fully applied lookup in a (potentially nested) mapping
       e.g. m[4][3] 
    """
    # the location in storage that holds the mapping (e.g. the m in m[4][3])
    loc: StorageLoc
    # the arguments to the mapping that give us an actual location in storage (e.g. the [4][3] in m[4][3])
    args: List[Exp]

    def is_equiv(self, other: StorageLoc) -> bool:
        if not isinstance(other, MappingLoc):
            return False
        if not self.loc.is_equiv(other.loc):
            return False
        if len(self.args) != len(other.args):
            return False
        for i in range(len(self.args)):
            if not self.args[i].is_equiv(other.args[i]):
                return False
        return True

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

    def is_equiv(self, other: StorageLoc) -> bool:
        if not isinstance(other, ContractLoc):
            return False
        if self.contract != other.contract:
            return False
        if self.field != other.field:
            return False
        if not self.loc.is_equiv(other.loc):
            return False
        return True


class Timing(metaclass=ABCMeta):
    """Is the storage varaible refering to the pre or post state"""

@dataclass
class Pre(Timing):
    """Prestate"""

@dataclass
class Post(Timing):
    """Poststate"""



# History Variables
@dataclass
class HistItem(Exp): 
    """Storage item relative to its path"""
    loc: StorageLoc
    hist: List[str]
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, HistItem):
            return False
        if self.type != other.type:
            return False
        if len(self.hist) != len(other.hist):
            return False
        for i in range(len(self.hist)):
            if self.hist[i] != other.hist[i]:
                return False
        if not self.loc.is_equiv(other.loc):
            return False
        return True

@dataclass
class HistVar(Exp): 
    """Variable relative to its path"""
    name: str
    hist: List[str]
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, HistVar):
            return False
        if self.type != other.type:
            return False
        if len(self.hist) != len(other.hist):
            return False
        for i in range(len(self.hist)):
            if self.hist[i] != other.hist[i]:
                return False
        if self.name != other.name:
            return False
        return True

@dataclass
class HistEnvVar(Exp): 
    """environment variable relative to its path"""
    name: str
    hist: List[str]
    type: ActType

    def is_equiv(self, other: Exp) -> bool:
        if not isinstance(other, HistEnvVar):
            return False
        if self.type != other.type:
            return False
        if len(self.hist) != len(other.hist):
            return False
        for i in range(len(self.hist)):
            if self.hist[i] != other.hist[i]:
                return False
        if self.name != other.name:
            return False
        return True


# all cnf functions

def translate2cnf(exp: Exp) -> Exp:

    basic = tocnf1(exp)

    in_nnf = nnf(basic)

    in_cnf = cnf(in_nnf)

    return in_cnf

def tocnf1(exp: Exp) -> Exp:

    if isinstance(exp, And):
        return And(tocnf1(exp.left), tocnf1(exp.right))

    elif isinstance(exp, Or):
        return Or(tocnf1(exp.left), tocnf1(exp.right))

    elif isinstance(exp, Not):
        return (Not(tocnf1(exp.value)))   
        
    elif isinstance(exp, Implies):
        return Or(Not(tocnf1(exp.left)), tocnf1(exp.right))

    elif isinstance(exp, ITE): 
        return ITE(translate2cnf(exp.condition), translate2cnf(exp.left), translate2cnf(exp.right), exp.type)

    elif isinstance(exp, Eq): 
        return Eq(translate2cnf(exp.left), translate2cnf(exp.right))

    elif isinstance(exp, Neq): 
        return Neq(translate2cnf(exp.left), translate2cnf(exp.right))

    else: 
        assert new_atom(exp) or isinstance(exp, InRange)
        return base_case(exp)
    
def base_case(exp: Exp) -> Exp:
    
    if exp.type != ActBool() and isinstance(exp, ITE):
        return ITE(translate2cnf(exp.condition), exp.left, exp.right, exp.type)
    
    elif isinstance(exp, InRange): 
        if isinstance(InRange.abitype, AbiIntType):
            min = -2**(InRange.abitype.size -1)
            max = 2**(InRange.abitype.size -1) -1
        elif isinstance(InRange.abitype, AbiUIntType):
            min = 0
            max = (2**InRange.abitype.size) -1
        elif isinstance(InRange.abitype, AbiAddressType):
            min = 0
            max = (2**256) -1
        else:
            assert False, "unsupported abitype for inrange"
        return And(Le(min, exp.expr), Le(exp.expr, max))

    else:
        return exp

def nnf(exp: Exp) -> Exp:

    if isinstance(exp, Not):
        if isinstance(exp.value, And):
            return Or(nnf(Not(exp.value.left)), nnf(Not(exp.value.right)))
        elif isinstance(exp.value, Or):
            return And(nnf(Not(exp.value.left)), nnf(Not(exp.value.right)))
        elif isinstance(exp.value, Not):
            return nnf(exp.value.value)
        elif isinstance(exp.value, Eq):
            return Neq(exp.value.left, exp.value.right)
        elif isinstance(exp.value, Neq):
            return Eq(exp.value.left, exp.value.right)
        else:
            return exp

    elif isinstance(exp, And):
        return And(nnf(exp.left), nnf(exp.right))
    elif isinstance(exp, Or):
        return Or(nnf(exp.left), nnf(exp.right))
    else:
        return exp

def cnf(exp: Exp) -> Exp:

    if is_cnf(exp):
        return exp
    else:
        if isinstance(exp, And):
            return And(cnf(exp.left), cnf(exp.right))
        else:
            assert isinstance(exp, Or)
            if isinstance(exp.left, And):
                return And(cnf(Or(exp.left.left, exp.right)), cnf(Or(exp.left.right, exp.right)))
            elif isinstance(exp.right, And):
                return And(cnf(Or(exp.left, exp.right.left)), cnf(Or(exp.left, exp.right.right)))
            else:
                return cnf(Or(cnf(exp.left), cnf(exp.right)))

def new_atom(exp: Exp) -> bool:

    if exp.type != ActBool():
        return True
        
    else: 
        atom = isinstance(exp, Lit) or isinstance(exp, Var) or isinstance(exp, EnvVar) or isinstance(exp, StorageItem) or \
                isinstance(exp, Le) or isinstance(exp, Lt) or isinstance(exp, Ge) or isinstance(exp, Gt) or \
                isinstance(exp, Eq) or isinstance(exp, Neq) 

        return atom  

def new_lit(exp: Exp) -> bool:
    if new_atom(exp):
        return True
    
    elif isinstance(exp, Not):
        assert new_atom(exp.value)
        return True
    
    elif isinstance(exp, Or):
        return new_lit(exp.left) and new_lit(exp.right)
    
    else:
        return False

def is_cnf(exp: Exp) -> bool:
    if new_lit(exp):
        return True
    elif isinstance(exp, And):
        return is_cnf(exp.left) and is_cnf(exp.right)
    else:
        return False

def to_cnf(exp: Exp) -> List[Exp]:
    cnf = translate2cnf(exp)
    return cnf2list(cnf)

def cnf2list(cnf: Exp) -> List[Exp]:
    if not isinstance(cnf, And):
        return [cnf]
    else:
        return cnf2list(cnf.left) + cnf2list(cnf.right)
    




# def cnf_exp(exp: Exp) -> Exp:

#     if is_atom(exp):
#         return exp
        
#     else:
#         if isinstance(exp, And):
#             return And(cnf_exp(exp.left), cnf_exp(exp.right))
        
#         elif isinstance(exp, Or):
#             if is_lit(exp): # literal is allowed to be a disj too (bc Or is defined to only have 2 args)
#                 return exp
#             elif is_lit(exp.left):
#                 if isinstance(exp.right, And):
#                     return And(cnf_exp(Or(exp.left, exp.right.left)), cnf_exp(Or(exp.left, exp.right.right)))
#                 else:
#                     return cnf_exp(Or(exp.left, cnf_exp(exp.right)))
#             elif is_lit(exp.right):
#                 if isinstance(exp.left, And):
#                     return And(cnf_exp(Or(exp.left.left, exp.right)), cnf_exp(Or(exp.left.right, exp.right)))
#                 else:
#                     return cnf_exp(Or(cnf_exp(exp.left), exp.right))or isinstance(exp, InRange)
#             if is_atom(exp.value):  
#                 return exp  
#             else:
#                 if isinstance(exp.value, And):
#                     return cnf_exp(Or(Not(exp.value.left), Not(exp.value.right)))
#                 elif isinstance(exp.value, Or):or isinstance(exp, InRange)
#                     return cnf_exp(exp.value.value)
#                 elif isinstance(exp, Implies):
#                     return And(cnf_exp(exp.value.left), cnf_exp(Not(exp.value.right)))
#                 elif isinstance(exp, Eq):
#                     return cnf_exp(Neq(exp.value.left, exp.value.right))
#                 elif isinstance(exp, Neq):
#                     return cnf_exp(Eq(exp.value.left, exp.value.right))
#                 else:
#                     return cnf_exp(Not(cnf_exp(exp.value)))   # lazy version for inrange and ITE
                
#         elif isinstance(exp, Implies):
#             return cnf_exp(Or(Not(exp.value.left), exp.value.right))

#         # ??
#         elif isinstance(exp, ITE): # translate the bool exp and ITEs into cnf 
#             passor isinstance(exp, InRange)
#             pass
#         else:
#             assert False, "unsupported exp: " + str(type(exp))


# def is_atom(exp: Exp) -> bool:

#     if exp.type != ActBool():
#         return not isinstance(exp, ITE)
        
#     else: 

#         # also consider eq neq with not bools an atom
#         atom = isinstance(exp, Lit) or isinstance(exp, Var) or isinstance(exp, EnvVar) or isinstance(exp, StorageItem) or \
#                 isinstance(exp, Le) or isinstance(exp, Lt) or isinstance(exp, Ge) or isinstance(exp, Gt)

#         if isinstance(exp, Eq) or isinstance(exp, Neq):
#             if exp.left.type != ActBool() and exp.right.type != ActBool():
#                 return True

#         return atom

# def is_lit(exp: Exp) -> bool:

#     if is_atom(exp):
#         return True
    
#     elif isinstance(exp, Not):
#         return is_atom(exp.value)
    
#     elif isinstance(exp, Or):
#         return is_lit(exp.left) and is_lit(exp.right)
    
#     else:
#         return False
    
