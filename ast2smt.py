from typing import Union, Set, Dict, List
from dataclasses import dataclass
from parse_act import *
from act_ast import *
import z3

Integer = Union[int, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
SymVar = Union[Integer, Boolean, z3.FuncDeclRef] #not sure about function type

# contract -> field name -> z3 variable
SymStore = Dict[str, Dict[str, SymVar]]
# var name -> z3 variable
SymEnv = Dict[str, Integer]
# var name -> z3 variable
SymCalldata = Dict[str, SymVar]

"""
x = z3.Int(<name>)                                              integer constant named <name>
z = z3.Bool(<name>)                                                     boolean constant named <name>
y = z3.Function(<fct_name>, <z3 input sort(s)>, <z3 ouput sort>)   uninterpreted function named <fct_name>

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



"""Returns the constraints from a behavior that are relevant for the consruction of the game tree"""
def extract_constraints(behv: Behavior) -> Set[Exp]:
    return set(behv.caseConditions + behv.preConditions + behv.stateUpdates)

def to_smt(env: SymEnv, calldata: SymCalldata, prestore: SymStore, history: List[str], exp: Exp) -> Integer | Boolean:
    if exp.type == ActBool:
        return generate_smt_constraint(exp, history)
    else:
        return generate_smt_term(exp, history)

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
            state[key][nested_key] = slottype2smt(nested_key, nested_value)
    
    smt_constraints = []
    for exp in extraConstraints:
        smt_constraints.append(generate_smt_constraint(exp), [])
    for exp in ctor.invariants:
        smt_constraints.append(generate_smt_constraint(exp), [])

    return SymState(state, set(smt_constraints))



def generate_tree(tree: Tree, behvs: Set[Behavior]) -> Tree:
    """recursively extends the tree by applying all behaviors to all leaves until no new reachable states are found"""
    pass
    


def slottype2smt(name: str, slot: SlotType) -> SymVar:
    if isinstance(slot, AbiIntType):
        return z3.Int(name)
    elif isinstance(slot, AbiUIntType):
        return z3.Int(name)
    elif isinstance(slot, AbiAddressType):
        return z3.Int(name)
    elif isinstance(slot, AbiBoolType):
        return z3.Bool(name)
    elif isinstance(slot, ContractType): #interpret contract as address?
        return z3.Int(name)
    elif isinstance(slot, MappingType):
        if slot.resultType == AbiBoolType:
            result = z3.BoolSort()
        elif slot.resultType in [AbiAddressType, AbiIntType, AbiUIntType, ContractType]:
            result = z3.IntSort()
        else:
            assert False, "unsupported result datatype: " + slot.resultType

        args = []
        for elem in slot.argsType:
            if isinstance(elem, AbiBoolType):
                args.append(z3.BoolSort())
            elif type(elem) in [AbiAddressType, AbiIntType, AbiUIntType, ContractType]:
                args.append(z3.IntSort())
            else:
                assert False, "unsupported argument datatype: " + elem

        return z3.Function(name, *args, result)




def generate_smt_constraint(exp: Exp, history: List[str]) -> Boolean:
    """
    LitBool
    VarBool
    EnvVarBool
    ??? StorageItem ???
    And
    Or
    Not
    Implies
    ITEBool
    Eq - KIM StorageItem
    Neq - KIM StorageItem
    InRange
    Lt
    Le
    Gt
    Ge
    """
    if isinstance(exp, Lit):
        return exp.value
    
    elif isinstance(exp, Var):
        label = to_label(history, exp.name)
        return z3.Bool(label)
    
    elif isinstance(exp, EnvVar):
        label = to_label(history, exp.name)
        return z3.Bool(label)
    
    elif isinstance(exp, StorageItem):
        
        result = generate_smt_storageloc(exp.loc, exp.type, history)
        if isinstance(exp.time, Post):
            return postbool(result)
        else:
            return result
    
    elif isinstance(exp, And):
        return z3.And(generate_smt_constraint(exp.left, history),
                      generate_smt_constraint(exp.right, history)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(generate_smt_constraint(exp.left, history), 
                     generate_smt_constraint(exp.right, history)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(generate_smt_constraint(exp.value, history))
    
    elif isinstance(exp, Implies):
        return z3.Implies(generate_smt_constraint(exp.left, history), 
                          generate_smt_constraint(exp.right, history)
                          )
    
    elif isinstance(exp, ITE):
        return z3.And(z3.Implies(
                            generate_smt_constraint(exp.condition, history), 
                            generate_smt_constraint(exp.left, history)),
                      z3.Implies(
                            z3.Not(generate_smt_constraint(exp.condition, history)),
                            generate_smt_constraint(exp.right, history))
                            )
    
    elif isinstance(exp, Eq):
        if isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool):
            return generate_smt_constraint(exp.left, history) == generate_smt_constraint(exp.right, history)
        elif isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt):
            return generate_smt_term(exp.left, history) == generate_smt_term(exp.right, history)
        else:
            assert False, "left and right have to be of the same type"

    elif isinstance(exp, Neq):
        if isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool):
            return z3.Not(
                          generate_smt_constraint(exp.left, history) == generate_smt_constraint(exp.right, history)
                          )
        elif isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt):
            return z3.Not(
                            generate_smt_term(exp.left, history) == generate_smt_term(exp.right, history)
                            )
        else:
            assert False, "left and right have to be of the same type"

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
                    generate_smt_constraint(Le(min, exp.expr), history),
                    generate_smt_constraint(Le(exp.expr, max), history)
                    )
    
    elif isinstance(exp, Lt):
        return generate_smt_constraint(exp.left, history) < generate_smt_constraint(exp.right, history)

    elif isinstance(exp, Le):
        return generate_smt_constraint(exp.left, history) <= generate_smt_constraint(exp.right, history)
    
    elif isinstance(exp, Gt):
        return generate_smt_constraint(exp.left, history) > generate_smt_constraint(exp.right, history)
    
    else:
        assert isinstance(exp, Ge)
        return generate_smt_constraint(exp.left, history) >= generate_smt_constraint(exp.right, history)





def generate_smt_term(exp: Exp, history: List[str]) -> Integer:
    """
    LitInt
    VarInt
    EnvVarInt
    ??? StorageItem ???
    Add
    Sub
    Mul
    Div
    Pow 
    ??? ITEInt ???
    """

    if isinstance(exp, Lit):
        return exp.value
    
    elif isinstance(exp, Var):
        return z3.Int(to_label(history, exp.name))
    
    elif isinstance(exp, EnvVar):
        return z3.Int(to_label(history, exp.name))
    
    elif isinstance(exp, StorageItem):
        result = generate_smt_storageloc(exp.loc, exp.type, history)
        if isinstance(exp.time, Post):
            return postint(result)
        else:
            return result

    elif isinstance(exp, Add):
        return generate_smt_term(exp.left, history) + generate_smt_term(exp.right, history)
    
    elif isinstance(exp, Sub):
        return generate_smt_term(exp.left, history) - generate_smt_term(exp.right, history)
    
    elif isinstance(exp, Mul):
        return generate_smt_term(exp.left, history) * generate_smt_term(exp.right, history)
    
    elif isinstance(exp, Div):
        return generate_smt_term(exp.left, history) / generate_smt_term(exp.right, history)
    
    elif isinstance(exp, Pow):
        left = generate_smt_term(exp.left, history)
        right = generate_smt_term(exp.right, history)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        # I am pretty sure that this is not correct SMT code:
        # x(6) == (if b then 8 else 20) ITE
        # x(6) == (b => 8) and (not b => 20)
        # should rather be 
        # (b => x(6) == 8) and (not b => x(6) == 20)
        assert isinstance(exp, ITE)
        return z3.If(exp.condition, exp.left, exp.right) # adapt
        # return z3.And(z3.Implies(
        #                     generate_smt_constraint(exp.condition, history), 
        #                     generate_smt_term(exp.left, history)),
        #             z3.Implies(
        #                     z3.Not(generate_smt_constraint(exp.condition, history)),
        #                     generate_smt_term(exp.right, history)))
        
def generate_smt_storageloc(loc: StorageLoc, ty: ActType, store: SymStore, history: List[str]) -> Union(Integer, Boolean):
    #do we need history?
        if isinstance(loc, VarLoc):
            isint = isinstance(ty, ActInt) and isinstance(store[loc.contract, loc.name], Integer)
            isbool = isinstance(ty, ActBool) and isinstance(store[loc.contract, loc.name], Boolean)
            assert isint or isbool, "types of storage and stored variable do not align"
            return store[loc.contract, loc.name]
        elif isinstance(loc, MappingLoc):
            smt_args = []
            for elem in loc.args:
                if isinstance(elem.type, ActInt): 
                    smt_args.append(generate_smt_term(elem, history))
                else:
                    smt_args.append(generate_smt_constraint(elem, history))

            return gen_mapping(loc.loc)(*smt_args)
        else:
            # ContractLoc case
            pass

def gen_mapping(loc: StorageLoc) -> z3.Function:    #not sure about type
    pass

def to_label(history: List[str], name: str) -> str:
    label = ""

    for elem in history:
        label = label + ";" + elem

    label = label + ";" + name
    return label



def from_label(label: str) -> (List[str], str):

    res = label.split(";")
    assert len(res)>0

    return res[:-1], res[-1]

"""
contract C {
  uint x;
  uint y;
  bool z;

  function(uint i, uint j) {
  
  }
}


"C": {
    x: AbiUintType(256),
    y: AbiUintType(256),
    z: AbiBoolType
}

---

"C": {
    x: z3.IntRef,
    y: z3.IntRef,
    z: z3.BoolRef
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
    

