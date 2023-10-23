from typing import Union, Set, Dict, List, Any, Tuple
from dataclasses import dataclass
from parse_act import *
from act_ast import *
import z3
import logging



# typing and datastructures

Integer = Union[int, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
SymVar = Union[Integer, Boolean, z3.FuncDeclRef] 

PreStore = Dict[str, Union[SymVar, 'PreStore']]
SymStore = Dict[str, PreStore]

"""
x = z3.Int(<name>): z3.ArithRef                                         integer constant named <name>
z = z3.Bool(<name>): z3.BoolRef                                                     boolean constant named <name>
y = z3.Function(<fct_name>, <z3 input sort(s)>, <z3 ouput sort>): z3.FuncDeclRef   uninterpreted function named <fct_name>

"""

@dataclass
class SymState:
    storage: SymStore
    constraints: List[Boolean]

@dataclass
class Tree:
    """a non-leaf node with children"""
    state: SymState
    children: Dict[str, 'Tree']
    case: List[Boolean]



# main functions

def contract2tree(contract: Contract, storage: Storage, extra_constraints: List[Exp]) -> Tree:
    """ translates the contract to the tree of all possible sequential executions of the differnt behaviors"""

    root = init_state(storage, contract.constructor, extra_constraints)
    
    return generate_tree([], root, [], [], contract.name, contract.constructor, contract.behaviors)


def init_state(storage: Storage, ctor: Constructor, extraConstraints: List[Exp]) -> SymState:
    """translate storage information to smt concepts, and collect initial constraints from user and invariants"""
    store: Dict = dict()
    for key, value in storage.items():
        store[key] = dict()
        for nested_key, nested_value in value.items():
            store[key][nested_key] = slottype2smt(key, nested_key, nested_value, storage)

    smt_constraints = []
    for exp in extraConstraints:
        smt_constraints.append(to_smt(store, store, [], exp))

    return SymState(store, smt_constraints)


def generate_tree(constraints: List[Boolean], 
                  prestate: SymState, 
                  case_cond: List[Boolean], 
                  history: List[str], 
                  contract_name: str, 
                  contr: Constructor, 
                  behvs: List[Behavior])             -> Tree:
    """recursively extends the tree by applying all behaviors to all leaves until no new reachable states are found"""

    children_solver = z3.Solver()
    children_solver.add(*prestate.constraints)
    children_solver.add(*constraints)
    children: Dict[str, Tree] = dict()
    for behv in behvs:
        child_name = behv.name + str(behv.caseConditions)
        # naive breaking condition: no 2 functions (behavior) can be called twice
        if not child_name in history:
            child, child_case = apply_behaviour(prestate, history + [child_name], contract_name, contr, behv)
            reachable = children_solver.check(child.constraints)
            if reachable == z3.sat:
                children[child_name] = generate_tree(constraints + prestate.constraints, 
                                                    child, 
                                                    child_case,
                                                    history + [child_name],
                                                    contract_name,
                                                    contr, 
                                                    behvs)
            elif reachable == z3.unknown:
                logging.info("solver returned 'unkown'")
                assert False
        
    return Tree(prestate, children, case_cond)


def slottype2smt(contract: str, name: str, slot: SlotType, storage: Storage) -> SymVar | PreStore :
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
        for key, value in storage[slot.contract].items():
            # key: str, value: SlotType
            smt_store[key] = slottype2smt(to_storage_label(contract, name), key, value, storage)
        return smt_store
        
    elif isinstance(slot, MappingType):
            if isinstance(slot.resultType, AbiBoolType):
                result = z3.BoolSort()
            elif type(slot.resultType) in [AbiAddressType, AbiIntType, AbiUIntType]:
                result = z3.IntSort()
            else:
                # to be extended to other datatypes later
                assert False, "unsupported result datatype: " + str(type(slot.resultType))

            args = []
            for elem in slot.argsType:
                if isinstance(elem, AbiBoolType):
                    args.append(z3.BoolSort())
                elif type(elem) in [AbiAddressType, AbiIntType, AbiUIntType]:
                    args.append(z3.IntSort())
                else:
                     # to be extended to other datatypes later
                    assert False, "unsupported argument datatype: " + str(type(elem))

            return z3.Function(to_storage_label(contract, name), *args, result)

    else:
        assert False, "unsupported abi datatype: " + str(type(slot))


def to_smt(prestore: SymStore, poststore: SymStore, history: List[str], exp: Exp) -> Integer | Boolean:
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
        return generate_smt_storageloc(prestore, poststore, history, exp.loc, exp.time) 
    
    # boolean expressions

    elif isinstance(exp, And):
        return z3.And(to_smt(prestore, poststore, history, exp.left),
                      to_smt(prestore, poststore, history, exp.right)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(to_smt(prestore, poststore, history, exp.left), 
                     to_smt(prestore, poststore, history, exp.right)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(to_smt(prestore, poststore, history, exp.value))
    
    elif isinstance(exp, Implies):
        return z3.Implies(to_smt(prestore, poststore, history, exp.left), 
                          to_smt(prestore, poststore, history, exp.right)
                          )
    
    elif isinstance(exp, ITE):
        return z3.If(to_smt(prestore, poststore, history, exp.condition),
                     to_smt(prestore, poststore, history, exp.left),
                     to_smt(prestore, poststore, history, exp.right)
                     )                   
    
    elif isinstance(exp, Eq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return to_smt(prestore, poststore, history, exp.left) == to_smt(prestore, poststore, history, exp.right)

    elif isinstance(exp, Neq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return z3.Not(to_smt(prestore, poststore, history, exp.left) == 
                      to_smt(prestore, poststore, history, exp.right))

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
                    to_smt(prestore, poststore, history, Le(min, exp.expr)),
                    to_smt(prestore, poststore, history, Le(exp.expr, max))
                    )
    
    elif isinstance(exp, Lt):
        return to_smt(prestore, poststore, history, exp.left) < \
               to_smt(prestore, poststore, history, exp.right)

    elif isinstance(exp, Le):
        return to_smt(prestore, poststore, history, exp.left) <= \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Gt):
        return to_smt(prestore, poststore, history, exp.left) > \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Ge):
        return to_smt(prestore, poststore, history, exp.left) >= \
               to_smt(prestore, poststore, history, exp.right)

    # integer expressions:
 
    elif isinstance(exp, Add):
        return to_smt(prestore, poststore, history, exp.left) + \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Sub):
        return to_smt(prestore, poststore, history, exp.left) - \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Mul):
        return to_smt(prestore, poststore, history, exp.left) * \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Div):
        return to_smt(prestore, poststore, history, exp.left) / \
               to_smt(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Pow):
        left = to_smt(prestore, poststore, history, exp.left)
        right = to_smt(prestore, poststore, history, exp.right)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        assert isinstance(exp, ITE)
        return z3.If(to_smt(prestore, poststore, history, exp.condition),
                    to_smt(prestore, poststore, history, exp.left),
                    to_smt(prestore, poststore, history, exp.right)) 
        

def apply_behaviour(state: SymState,
                    history: List[str], 
                    contract_name: str, 
                    contr: Constructor,
                    behv: Behavior)         -> Tuple[SymState, List[Boolean]]:
    """apply behavior 'behv' to the state 'state', returns a the SymState (storage state and constraints) after this execution"""

    new_storage = dict()
    for key, value in state.storage.items():
        new_storage[key] = gen_poststore(value, history[-1])
    

    constraints = []
    case_cond = []
    for exp in behv.caseConditions:
        case_cond.append(to_smt(state.storage, new_storage, history, exp))
    constraints.extend(case_cond)
    for exp in behv.preConditions:
        constraints.append(to_smt(state.storage, new_storage, history, exp))
    for exp in behv.postConditions:
        constraints.append(to_smt(state.storage, new_storage, history, exp))
    for exp in contr.invariants:
        constraints.append(to_smt(state.storage, new_storage, history, exp))
    for exp in behv.stateUpdates:
        constraints.append(to_smt(state.storage, new_storage, history, exp))
   
    no_update_constraints = no_update(state.storage, new_storage, history, contract_name ,behv.stateUpdates)

    return SymState(new_storage, constraints + no_update_constraints), case_cond


def generate_smt_storageloc(
                            prestore: SymStore,
                            poststore: SymStore,
                            history: List[str], 
                            loc: StorageLoc,
                            time: Timing)      ->     SymVar:
        """returns the correct smt variable from the SymStore"""

        if time == Pre():
            store = prestore
        else:
            store = poststore

        if isinstance(loc, VarLoc):
            return store[loc.contract][loc.name]
        
        elif isinstance(loc, MappingLoc):
            smt_args = []
            for elem in loc.args:
                smt_args.append(to_smt(prestore, poststore, history, elem))

            func = generate_smt_storageloc(prestore, poststore, history, loc.loc, time)
            assert isinstance(func, z3.FuncDeclRef)
            return func(*smt_args) 
        
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

            return walk_the_storage(store[collect_list_of_keys[0]], collect_list_of_keys[1:])


def gen_poststore(pre: PreStore, name: str) -> PreStore:
    post = dict()

    for key, value in pre.items():
        if not isinstance(value, Dict):
            # base case, we hit a SymVar:
            if isinstance(value, z3.FuncDeclRef):
                z3sorts = []
                arity = value.arity()
                for i in range(arity):
                    if value.domain(i) == bool:
                        z3sorts.append(z3.BoolSort()) 
                    elif value.domain(i) == int:
                        z3sorts.append(z3.IntSort())
                    else: 
                        assert False, "sorts other than int or bool not supported"
                if value.range() == bool:
                    z3sorts.append(z3.BoolSort()) 
                elif value.range() == int:
                    z3sorts.append(z3.IntSort())
                else: 
                    assert False, "sorts other than int or bool not supported"

                post[key] = z3.Function(name + "_" + value.name(), *z3sorts) 
            
            elif isinstance(value, z3.ArithRef):
                post[key] = z3.ArithRef(name + "_" + value.decl().name())
            elif isinstance(value, z3.BoolRef):
                post[key] = z3.BoolRef(name + "_" + value.decl().name())
            else: 
                assert False, "storage items have to be either z3 bool, z3 int or z3 functions"
        else:
            post[key] = gen_poststore(value, name)

    return post


def no_update(prestore: SymStore, poststore: SymStore, history: List[str], main_contr: str, updates: List[Exp]) -> List[Boolean]:
    """Identifies all SymVars from poststore that are not assigned a new value in the updates contraints.
    Returns a list of constraints that assert the not-updated poststore Symvars have the same value as the 
    respective prestore symvars.
    Only add the constraints for the main contract, others irrelevant
    """

    noup_all = copy_symstore(prestore)
    # delete redundant info - variables of other than main contract, the accessed ones will appear in a nested dict 
    noup = noup_all[main_contr]
    supp_fctargs: Dict[List[str], List[List[Integer | Boolean]]] = dict() 


    for update in updates:
        assert isinstance(update, Eq)
        item = update.left
        assert isinstance(item, StorageItem)
        loc = item.loc

        # search loc in postStore
        if isinstance(loc, VarLoc):
            assert isinstance(noup, Dict)
            del noup[loc.name]
        elif isinstance(loc, MappingLoc):
            keys: List[str] = []
            new_loc = loc.loc
            while isinstance(new_loc, ContractLoc):
                # contractloc case:
                keys = [new_loc.field] + keys
                new_loc = new_loc.loc
            #varloc case:
            assert isinstance(new_loc, VarLoc)
            keys = [new_loc.name] + keys
            if keys in supp_fctargs:
                supp_fctargs[keys].append([to_smt(prestore, poststore, history, elem) for elem in loc.args])
            else:
                supp_fctargs[keys] = [[to_smt(prestore, poststore, history, elem) for elem in loc.args]]
        else: 
            # contractloc case
            keys = []
            while isinstance(loc, ContractLoc):
                keys = [loc.field] + keys
                loc = loc.loc
            # reached varloc
            assert isinstance(loc, VarLoc)
            keys = [loc.name] + keys
            store = noup #shallow copy on purpose
            last_key = keys[-1]
            keys = keys[:-1]
            for elem in keys:
                assert isinstance(store, Dict)
                store = store[elem]

            assert isinstance(store, Dict)
            del store[last_key] # through call by reference noup was shrinked as intended

    assert isinstance(noup, Dict)
    constraints = noup_cons(noup, poststore[main_contr], supp_fctargs, [])

    return constraints


def noup_cons(prestore: PreStore,
              poststore: PreStore, 
              fsupp: Dict[ List[str],List[List[Integer | Boolean]]],
              path: List[str]
              )                                                    -> List[Boolean]:

    constraints = []
    for key, value in prestore.items():    
        if isinstance(value, int) or z3.is_int(value) \
            or isinstance(value, bool) or z3.is_bool(value):
            constraints.append(poststore[key] == value)
        elif isinstance(value, z3.FuncDeclRef):
            constraints.append(func_update(value, poststore[key], fsupp[path + [key]]))
        else:
            assert isinstance(poststore[key], Dict)
            assert isinstance(value, Dict)
            constraints.extend(noup_cons(value, poststore[key], fsupp, path + [key]))

    return constraints


def func_update(pref: z3.FuncDeclRef, postf: z3.FuncDeclRef, exc: List[List[Integer | Boolean]]) -> Boolean:
    """ construct forall quantified formula stating 'pref'=='postf' everywhere except on the 'exc' points"""
    
    fresh_vars = []
    assert pref.arity() == postf.arity(), "functions incompatible, different arities"
    for i in range(pref.arity()):
        assert pref.domain(i) == postf.domain(i), "functions incompatible, different domain types"
        if pref.domain(i) == z3.IntSort():
            fresh_vars.append(z3.FreshInt())
        elif pref.domain(i) == z3.BoolSort():
            fresh_vars.append(z3.FreshBool())
        else:
            assert False, "unsupported type" + pref.domain(i)

    conjuncts = []
    for elem in exc:
        equ = []
        for i in range(len(fresh_vars)):
            assert z3.is_int(elem[i]) == z3.is_int(fresh_vars[i]), "incompatible argument types"
            assert z3.is_bool(elem[i]) == z3.is_bool(fresh_vars[i]), "incompatible argument types"
            equ.append(elem[i] == fresh_vars[i])
        conjuncts.append(z3.And(*equ))

    lhs = z3.Not(z3.Or(*conjuncts))
    rhs = postf(*fresh_vars) == pref(*fresh_vars)

    return z3.ForAll(fresh_vars, z3.Implies(lhs, rhs))



# "little" helper functions

def copy_symstore(store: SymStore) -> SymStore:

    scopy = dict()
    for key, value in store.items():
        scopy[key] = copy_prestore(value)

    return scopy

def copy_prestore(store: PreStore) -> PreStore:

    scopy: PreStore = dict()
    for key, value in store.items():
        if isinstance(value, Dict):
            scopy[key] = copy_prestore(value)
        else:
            scopy[key] = value
    return scopy

def walk_the_storage(store: PreStore, keys: List) -> SymVar:
    
    isint = isinstance(store[keys[0]], int)
    isintsort = z3.is_int(store[keys[0]])
    isbool = isinstance(store[keys[0]], bool)
    isboolsort = z3.is_bool(store[keys[0]])
    isfun = isinstance(store[keys[0]], z3.FuncDeclRef)
    issymvar = isfun or isint or isintsort or isbool or isboolsort
    if len(keys)==1:
        assert issymvar, "contradicting types" 
        return store[keys[0]]
    else:
        if isinstance(store[keys[0]], Dict):
            return walk_the_storage(store[keys[0]], keys[1:])
        else:
            assert False, "incompatible PreStore and keys list"

def to_label(history: List[str], name: str) -> str:
    label = ""

    for elem in history:
        label = label + ";" + elem

    label = label + ";" + name
    return label

def from_label(label: str) -> Tuple[List[str], str]:

    res = label.split(";")
    assert len(res) > 0

    return res[:-1], res[-1]

def to_storage_label(contract: str, name: str) -> str:
    return contract + "." + name

