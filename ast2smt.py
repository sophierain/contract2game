from typing import Union, Set, Dict, List, Any
from dataclasses import dataclass
from parse_act import *
from act_ast import *
import z3

Integer = Union[int, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
SymVar = Union[Integer, Boolean, z3.FuncDeclRef] 

# generic contract -> field name -> z3 variable
# or generic contract -> instantiated contract ... -> field name -> z3.variable
SymStore = Dict[str, Dict[str, SymVar | Dict[str, Any]]]


#not sure we need this, does z3 create distinct variables if their names are identical?
# var name -> z3 variable
SymEnv = Dict[str, Integer]
# var name -> z3 variable
SymCalldata = Dict[str, SymVar]

"""
x = z3.Int(<name>): z3.ArithRef                                         integer constant named <name>
z = z3.Bool(<name>): z3.BoolRef                                                     boolean constant named <name>
y = z3.Function(<fct_name>, <z3 input sort(s)>, <z3 ouput sort>): z3.FuncDeclRef   uninterpreted function named <fct_name>

"""

postint = z3.Function("postint", z3.IntSort(), z3.IntSort())
postbool = z3.Function("postbool", z3.BoolSort(), z3.BoolSort())


@dataclass
class SymState:
    storage: SymStore
    constraints: Set[z3.BoolRef]


class BaseTree(metaclass=ABCMeta):
    """base class for game trees"""

@dataclass
class Tree(BaseTree):
    """a non-leaf node with children"""
    state: SymState
    children: Dict[str, BaseTree]




def extract_constraints(behv: Behavior) -> Set[Exp]:
    """Returns the constraints from a behavior that are relevant for the consruction of the game tree"""
    return set(behv.caseConditions + behv.preConditions + behv.stateUpdates)


def apply_behaviour(state: SymState, behv: Behavior) -> SymState:
    pass



def reachable(state: SymState) -> z3.CheckSatResult:
    pass


def init_state(storage: Storage, ctor: Constructor, extraConstraints: Set[Exp]) -> SymState:
    """translate storage information to smt concepts, and collect initial constraints from user and invariants"""
    state = dict()
    for key, value in storage.items():
        state[key] = dict()
        for nested_key, nested_value in value.items():
            state[key][nested_key] = slottype2smt(key, nested_key, nested_value, storage)
    
    smt_constraints = []
    for exp in extraConstraints:
        smt_constraints.append(to_smt(exp, []))
    for exp in ctor.invariants:
        smt_constraints.append(to_smt(exp, []))

    return SymState(state, set(smt_constraints))



def generate_tree(tree: Tree, behvs: Set[Behavior]) -> Tree:
    """recursively extends the tree by applying all behaviors to all leaves until no new reachable states are found"""
    pass
    


def slottype2smt(contract: str, name: str, slot: SlotType, storage: Storage) -> SymVar | Dict :
    '''needed to keep track of all smt declarations for the storage'''
    var_name = to_storage_label(contract, name)
    if isinstance(slot, AbiIntType):
        return z3.Int(var_name)
    elif isinstance(slot, AbiUIntType):
        return z3.Int(var_name)
    elif isinstance(slot, AbiAddressType):
        return z3.Int(var_name)
    elif isinstance(slot, AbiBoolType):
        return z3.Bool(var_name)


    elif isinstance(slot, ContractType): 
        assert slot.contract in storage #repeat stuff with storage[slot.contract] and add contract to the storage label
        smt_store = dict()
        for key, value in storage[slot.contract]:
            smt_store[key] = slottype2smt(to_storage_label(contract, name), key, value, storage[slot.contract])
        return smt_store
        
    elif isinstance(slot, MappingType):
            if isinstance(slot.resultType, AbiBoolType):
                result = z3.BoolSort()
            elif type(slot.resultType) in [AbiAddressType, AbiIntType, AbiUIntType]:
                result = z3.IntSort()
            else:
                # to be extended to other datatypes later
                assert False, "unsupported result datatype: " + type(slot.resultType)

            args = []
            for elem in slot.argsType:
                if isinstance(elem, AbiBoolType):
                    args.append(z3.BoolSort())
                elif type(elem) in [AbiAddressType, AbiIntType, AbiUIntType]:
                    args.append(z3.IntSort())
                else:
                     # to be extended to other datatypes later
                    assert False, "unsupported argument datatype: " + type(elem)

            return z3.Function(to_storage_label(contract, name), *args, result)

    else:
        assert False, "unsupported abi datatype: " + type(slot)



# remove env and calldata
def to_smt(env: SymEnv, calldata: SymCalldata, store: SymStore, history: List[str], exp: Exp) -> Integer | Boolean: # type checking!
    """
    supported Boolean operations:
        Lit
        Var
        EnvVar
        StorageItem
        And
        Or
        Not
        Implies
        ITE
        Eq 
        Neq 
        InRange
        Lt
        Le
        Gt
        Ge
    supported Integer operations:  
        LitInt
        VarInt
        EnvVarInt
        StorageItem
        Add
        Sub
        Mul
        Div
        Pow 
        ITE
    """
    # variables, constants, functions

    if isinstance(exp, Lit):
        return exp.value
    
    elif isinstance(exp, Var): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(history, exp.name))
        else:
            return z3.Int(to_label(history, exp.name))
    
    elif isinstance(exp, EnvVar): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(history, exp.name))
        else:
            return z3.Int(to_label(history, exp.name))
       
    elif isinstance(exp, StorageItem):
        result = generate_smt_storageloc(env, calldata, store, history, exp.loc)
        if isinstance(exp.time, Post):
            if isinstance(exp.type. ActBool):
                return postbool(result)
            else:
                 return postint(result)
        else:
            return result
    
    # boolean expressions

    elif isinstance(exp, And):
        return z3.And(to_smt(env, calldata, store, history, exp.left),
                      to_smt(env, calldata, store, history, exp.right)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(to_smt(env, calldata, store, history, exp.left), 
                     to_smt(env, calldata, store, history, exp.right)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(to_smt(env, calldata, store, history, exp.value))
    
    elif isinstance(exp, Implies):
        return z3.Implies(to_smt(env, calldata, store, history, exp.left), 
                          to_smt(env, calldata, store, history, exp.right)
                          )
    
    elif isinstance(exp, ITE):
        return z3.If(to_smt(env, calldata, store, history, exp.condition),
                     to_smt(env, calldata, store, history, exp.left),
                     to_smt(env, calldata, store, history, exp.right)
                     )                   
    
    elif isinstance(exp, Eq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return to_smt(env, calldata, store, history, exp.left) == to_smt(env, calldata, store, history, exp.right)

    elif isinstance(exp, Neq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return z3.Not(to_smt(env, calldata, store, history, exp.left) == 
                      to_smt(env, calldata, store, history, exp.right))

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
        return z3.And(
                    to_smt(env, calldata, store, history, Le(min, exp.expr)),
                    to_smt(env, calldata, store, history, Le(exp.expr, max))
                    )
    
    elif isinstance(exp, Lt):
        return to_smt(env, calldata, store, history, exp.left) < \
               to_smt(env, calldata, store, history, exp.right)

    elif isinstance(exp, Le):
        return to_smt(env, calldata, store, history, exp.left) <= \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Gt):
        return to_smt(env, calldata, store, history, exp.left) > \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Ge):
        return to_smt(env, calldata, store, history, exp.left) >= \
               to_smt(env, calldata, store, history, exp.right)

    # integer expressions:
 
    elif isinstance(exp, Add):
        return to_smt(env, calldata, store, history, exp.left) + \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Sub):
        return to_smt(env, calldata, store, history, exp.left) - \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Mul):
        return to_smt(env, calldata, store, history, exp.left) * \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Div):
        return to_smt(env, calldata, store, history, exp.left) / \
               to_smt(env, calldata, store, history, exp.right)
    
    elif isinstance(exp, Pow):
        left = to_smt(env, calldata, store, history, exp.left)
        right = to_smt(env, calldata, store, history, exp.right)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        assert isinstance(exp, ITE)
        return z3.If(to_smt(env, calldata, store, history, exp.condition),
                    to_smt(env, calldata, store, history, exp.left),
                    to_smt(env, calldata, store, history, exp.right)) 
        



def generate_smt_storageloc(env: SymEnv,
                            calldata: SymCalldata,
                            store: SymStore, 
                            history: List[str], 
                            loc: StorageLoc)      ->     SymVar:
        """returns the correct smt variable from the SymStore"""
        if isinstance(loc, VarLoc):
            return store[loc.contract][loc.name]
        
        elif isinstance(loc, MappingLoc):
            smt_args = []
            for elem in loc.args:
                smt_args.append(to_smt(env, calldata, store, history, elem))

            func = generate_smt_storageloc(env, calldata, store, history, loc.loc)
            return func(*smt_args)  # not sure this works
        
        else:
            assert isinstance(loc, ContractLoc)
            collect_list_of_keys = [loc.field]
            while not isinstance(loc.loc, VarLoc):
                loc = loc.loc
                if isinstance(loc, ContractLoc):
                    collect_list_of_keys = [loc.field] + collect_list_of_keys
                else:
                    assert False, "mappings returning contracts is currently not implemented"
            collect_list_of_keys = [loc.loc.name] + collect_list_of_keys

            return walk_the_storage(store, collect_list_of_keys)
        


def walk_the_storage(store: SymStore | Dict[str, SymVar] | SymVar, keys: List) -> \
                                                    SymStore | SymVar | Dict[str, SymVar]:
    if len(keys)==1:
        assert isinstance(store[keys[0]], SymVar), "contradicting types" 
        return store[keys[0]]
    else:
        return walk_the_storage(store[keys[0]], keys[1:])


def to_label(history: List[str], name: str) -> str:
    label = ""

    for elem in history:
        label = label + ";" + elem

    label = label + ";" + name
    return label



def from_label(label: str) -> (List[str], str):

    res = label.split(";")
    assert len(res) > 0

    return res[:-1], res[-1]

def to_storage_label(contract: str, name: str) -> str:
    return contract + "." + name

"""
contract C {
  uint x;
  uint y;
  bool z;

  function f(uint , uint) -> uint {
  
  }
}


"C": {
    x: AbiUintType(256),
    y: AbiUintType(256),
    z: AbiBoolType
}

---

"C": {
    "x": z3.IntRef C.x,
    "y": z3.IntRef C.y,
    "z": z3.BoolRef C.z
}

0 <= x <= 2^256
0 <= y <= 2^256

"""



# @dataclass
# class SMT_Behavior:
#     name: str
#     caseConditions: Boolean
#     preConditions: Boolean
#     postConditions: Boolean
#     stateUpdates: Boolean

# @dataclass
# class SMT_Contract:
#     name: str
#     behaviors: List[SMT_Behavior]

# def act_to_smt(act: Act) -> List[SMT_Contract]:
#     return [contract_to_smt(elem, act["store"]) for elem in act["contracts"]]

# def contract_to_smt(contract: Contract, store: Storage) -> SMT_Contract:
#     return SMT_Contract(contract["name"], [behavior_to_smt(elem, contract["constructor"], store) for elem in contract["behaviors"]])

# def behavior_to_smt(behv: Behavior, contr: Constructor, store: Storage) -> SMT_Behavior:

#     case = conjunction(*[generate_constraint(elem, contr, store) for elem in behv["caseConditions"]])
#     pre = conjunction(*[generate_constraint(elem, contr, store) for elem in behv["preConditions"]])
#     post = conjunction(*[generate_constraint(elem, contr, store) for elem in behv["postConditions"]])
#     updates = conjunction(*[generate_constraint(elem, contr, store) for elem in behv["stateUpdates"]])

#     return SMT_Behavior(behv["name"], case, pre, post, updates)

# def generate_constraint(boolexp: BoolExp, contr: Constructor, store: Storage) -> Boolean:
#     # are Contructor and Storage needed for our purpose?
    
#     if isinstance(boolexp, LitBool):
#         return boolexp["value"]
#     elif isinstance(boolexp, VarBool):
#         return z3.Bool(boolexp["name"])
    

