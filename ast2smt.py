from typing import Union, Set, Dict, List, Any, Tuple
from dataclasses import dataclass
from parse_act import *
from act_ast import *
import z3
import logging


# typing and datastructures

Integer = Union[int, z3.ArithRef]
Boolean = Union[bool, z3.BoolRef]
String = Union[str, z3.SeqRef]
SymVar = Union[Integer, Boolean, String, z3.FuncDeclRef] 
#is_string, is_int, is_bool are the type check calls

PreStore = Dict[str, Union[SymVar, 'PreStore']]
SymStore = Dict[str, PreStore]

"""
x = z3.Int(<name>): z3.ArithRef                                         integer constant named <name>
z = z3.Bool(<name>): z3.BoolRef   
s = z3.String(<name>): z3.SeqRef                                                  boolean constant named <name>
y = z3.Function(<fct_name>, <z3 input sort(s)>, <z3 ouput sort>): z3.FuncDeclRef   uninterpreted function named <fct_name>
"""

@dataclass
class SymState:
    storage: SymStore
    constraints: List[Boolean]

@dataclass
class Tree:
    """a node with possibly 0 children"""
    state: SymState
    children: Dict[str, 'Tree']
    case: List[Boolean]

    def __repr__(self, level = 0) -> str:
        
        indent = "   "*level
        res = f"{indent}State: \n"
        res = res + f"{indent}   Storage:\n"
        for key, value in self.state.storage.items():
            res = res + f"      {indent}{key}: {value}\n"
        res = res + f"{indent}   Constraints:\n"
        for elem in self.state.constraints:
            res = res + f"{indent}      {elem}\n"
        res = res + f"{indent}Children:\n"
        for ckey, cvalue in self.children.items():
            res = res + f"{indent}   {ckey}:\n{cvalue.__repr__(level + 1)}\n"
        res = res +f"{indent}Case:"
        for elem in self.case:
            res = res + f"\n{indent}   {elem}"

        return res

    def structure(self, level: int = 0):
        for key, value in self.children.items():
                print(level*"   " + key)
                value.structure(level + 1)
        return

# main functions

def contract2tree(contract: Contract, storage: Storage, extra_constraints: List[Exp]) -> Tree:
    """ 
    contract: contract to be analyzed
    storage: storage dict of contract, contains all variables to be considered
    extra_constraints: a list of user defined constraints to be enforced as preconditions

    returns: a tree containg all possible sequential executions of the differnt behaviors of the contract
    
    """

    root = init_state(storage, contract.constructor, extra_constraints)
    
    return generate_tree([], root.storage, root, [], [], contract.name, contract.constructor, contract.behaviors)


def init_state(storage: Storage, ctor: Constructor, extraConstraints: List[Exp]) -> SymState:
    """
    storage: storage dict of contract, contains all variables to be considered
    ctor: constructor of the contract, might be used later
    extra_constraints: a list of user defined constraints to be enforced as preconditions

    returns: a symstate containing translated storage information to smt concepts, 
             and collected initial constraints from user
    
    """
    store: Dict = dict()
    for key, value in storage.items():
        store[key] = dict()
        for nested_key, nested_value in value.items():
            store[key][nested_key] = slottype2smt(key, nested_key, nested_value, storage)

    smt_constraints = []
    for exp in extraConstraints:
        smt_constraints.append(to_bool(store, store, [], exp))

    return SymState(store, smt_constraints)


def generate_tree(
                  constraints: List[Boolean], 
                  initstore: SymStore,
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
        child_name = behv.name + "__" + to_node_name(behv.caseConditions, initstore)
        # naive breaking condition: no 2 functions (behavior) can be called twice
        if not child_name in history:
            child, child_case = apply_behaviour(prestate, history + [child_name], contract_name, contr, behv)
            reachable = children_solver.check(child.constraints)
            if reachable == z3.sat:
                children[child_name] = generate_tree(constraints + prestate.constraints, 
                                                     initstore,
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
    elif isinstance(slot, AbiStringType):
        return z3.String(var_name)

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
            elif type(slot.resultType) == AbiStringType:
                result = z3.StringSort()
            else:
                # to be extended to other datatypes later
                assert False, "unsupported result datatype: " + str(type(slot.resultType))

            args = []
            for elem in slot.argsType:
                if isinstance(elem, AbiBoolType):
                    args.append(z3.BoolSort())
                elif type(elem) in [AbiAddressType, AbiIntType, AbiUIntType]:
                    args.append(z3.IntSort())
                elif type(elem) == AbiStringType:
                    args.append(z3.StringSort())
                else:
                     # to be extended to other datatypes later
                    assert False, "unsupported argument datatype: " + str(type(elem))

            return z3.Function(to_storage_label(contract, name), *args, result)

    else:
        assert False, "unsupported abi datatype: " + str(type(slot))


def to_bool(prestore: SymStore, poststore: SymStore, history: List[str], exp: Exp) -> Boolean:
    res = to_smt(prestore, poststore, history, exp)
    assert isinstance(res, bool) or isinstance(res, z3.BoolRef), "boolean expression expected"
    return res


def to_int(prestore: SymStore, poststore: SymStore, history: List[str], exp: Exp) -> Integer:
    res = to_smt(prestore, poststore, history, exp)
    assert isinstance(res, int) or isinstance(res, z3.ArithRef), "integer expression expected"
    return res


def to_smt(prestore: SymStore, poststore: SymStore, history: List[str], exp: Exp) -> Integer | Boolean | String:
    """
    supported operations:
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

        Add
        Sub
        Mul
        Div
        Pow 
    """
    # variables, constants, functions

    if isinstance(exp, Lit):
        return exp.value
    
    elif isinstance(exp, Var): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(history, exp.name))
        elif isinstance(exp.type, ActByteStr):
            return z3.String(to_label(history, exp.name))
        else:
            return z3.Int(to_label(history, exp.name))
    
    elif isinstance(exp, EnvVar): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(history, exp.name))
        elif isinstance(exp.type, ActByteStr):
            return z3.String(to_label(history, exp.name))
        else:
            return z3.Int(to_label(history, exp.name))
       
    elif isinstance(exp, StorageItem):
        gen_storeloc = generate_smt_storageloc(prestore, poststore, history, exp.loc, exp.time) 
        assert not isinstance(gen_storeloc, z3.FuncDeclRef)
        return gen_storeloc
    
    # boolean expressions

    elif isinstance(exp, And):
        return z3.And(to_bool(prestore, poststore, history, exp.left),
                      to_bool(prestore, poststore, history, exp.right)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(to_bool(prestore, poststore, history, exp.left), 
                     to_bool(prestore, poststore, history, exp.right)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(to_bool(prestore, poststore, history, exp.value))
    
    elif isinstance(exp, Implies):
        return z3.Implies(to_bool(prestore, poststore, history, exp.left), 
                          to_bool(prestore, poststore, history, exp.right)
                          )
    
    elif isinstance(exp, ITE):
        return z3.If(to_bool(prestore, poststore, history, exp.condition),
                     to_smt(prestore, poststore, history, exp.left),
                     to_smt(prestore, poststore, history, exp.right)
                     )                   
    
    elif isinstance(exp, Eq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        both_bytestr = isinstance(exp.left.type, ActByteStr) and isinstance(exp.right.type, ActByteStr)
        assert both_bool or both_int or both_bytestr, "left and right have to be of the same type"
        return to_smt(prestore, poststore, history, exp.left) == to_smt(prestore, poststore, history, exp.right)

    elif isinstance(exp, Neq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        both_bytestr = isinstance(exp.left.type, ActByteStr) and isinstance(exp.right.type, ActByteStr)
        assert both_bool or both_int or both_bytestr, "left and right have to be of the same type"
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
                    to_bool(prestore, poststore, history, Le(min, exp.expr)),
                    to_bool(prestore, poststore, history, Le(exp.expr, max))
                    )
    
    elif isinstance(exp, Lt):
        return to_int(prestore, poststore, history, exp.left) < \
               to_int(prestore, poststore, history, exp.right)

    elif isinstance(exp, Le):
        return to_int(prestore, poststore, history, exp.left) <= \
               to_int(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Gt):
        return to_int(prestore, poststore, history, exp.left) > \
               to_int(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Ge):
        return to_int(prestore, poststore, history, exp.left) >= \
               to_int(prestore, poststore, history, exp.right)

    # integer expressions:
 
    elif isinstance(exp, Add):
        return to_int(prestore, poststore, history, exp.left) + \
               to_int(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Sub):
        return to_int(prestore, poststore, history, exp.left) - \
               to_int(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Mul):
        return to_int(prestore, poststore, history, exp.left) * \
               to_int(prestore, poststore, history, exp.right)
    
    elif isinstance(exp, Div):
        nom = to_int(prestore, poststore, history, exp.left)
        div = to_int(prestore, poststore, history, exp.left)
        if type(nom) == int and type(div) == int:
            return int(nom / div)
        else:
            res = nom / div
            assert isinstance(res, z3.ArithRef)
            return res

    
    elif isinstance(exp, Pow):
        left = to_int(prestore, poststore, history, exp.left)
        right = to_int(prestore, poststore, history, exp.right)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        assert False 
     

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
        case_cond.append(to_bool(state.storage, new_storage, history, exp))
    constraints.extend(case_cond)
    for exp in behv.preConditions:
        constraints.append(to_bool(state.storage, new_storage, history, exp))
    for exp in behv.postConditions:
        constraints.append(to_bool(state.storage, new_storage, history, exp))
    for exp in contr.invariants:
        constraints.append(to_bool(state.storage, new_storage, history, exp))
    for exp in behv.stateUpdates:
        constraints.append(to_bool(state.storage, new_storage, history, exp))
   
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
            var = store[loc.contract][loc.name]
            assert not isinstance(var, Dict)
            return var
        
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
            print("orange")
            collect_list_of_keys = [loc.loc.contract, loc.loc.name] + collect_list_of_keys

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
                    z3sorts.append(value.domain(i)) 
                z3sorts.append(value.range())
                post[key] = z3.Function(name + "_" + value.name(), *z3sorts) 
            
            elif z3.is_int(value):
                assert isinstance(value, z3.ArithRef)
                post[key] = z3.Int(name + "_" + value.decl().name())
            elif z3.is_bool(value):
                assert isinstance(value, z3.BoolRef)
                post[key] = z3.Bool(name + "_" + value.decl().name())
            elif z3.is_string(value):
                assert isinstance(value, z3.SeqRef)
                post[key] = z3.String(name + "_" + value.decl().name())
            else: 
                assert False, "unsupported z3 type: " + str(type(value))
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
    supp_fctargs: Dict[str, List[List[Integer | Boolean | String]]] = dict() 


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
            keys: str = ""
            new_loc = loc.loc
            while isinstance(new_loc, ContractLoc):
                # contractloc case:
                if keys == "":
                    keys = new_loc.field
                else:
                    keys = new_loc.field + "_" + keys
                new_loc = new_loc.loc
            #varloc case:
            assert isinstance(new_loc, VarLoc)
            keys = new_loc.name + "_" + keys
            if keys in supp_fctargs:
                supp_fctargs[keys].append([to_smt(prestore, poststore, history, elem) for elem in loc.args])
            else:
                supp_fctargs[keys] = [[to_smt(prestore, poststore, history, elem) for elem in loc.args]]
        else: 
            # contractloc case
            key_list: List[str] = []
            while isinstance(loc, ContractLoc):
                key_list = [loc.field] +  key_list
                loc = loc.loc
            # reached varloc
            assert isinstance(loc, VarLoc)
            key_list = [loc.name] + key_list
            store: SymVar | PreStore = noup #shallow copy on purpose
            last_key = key_list[-1]
            key_list = key_list[:-1]
            for elem in key_list:
                assert isinstance(store, Dict)
                assert elem in store
                store = store[elem]

            assert isinstance(store, Dict)
            del store[last_key] # through call by reference noup was shrinked as intended

    assert isinstance(noup, Dict)
    constraints = noup_cons(noup, poststore[main_contr], supp_fctargs, "")

    return constraints


def noup_cons(prestore: PreStore,
              poststore: PreStore, 
              fsupp: Dict[str, List[List[Integer | Boolean | String]]],
              path: str
              )                                                    -> List[Boolean]:

    constraints = []
    for key, value in prestore.items():  
        if path == "":
            path = key
        else:
            path = path + "_" + key  

        if isinstance(value, int) or z3.is_int(value) \
            or isinstance(value, bool) or z3.is_bool(value):
            assert not isinstance(poststore[key], Dict)
            constraints.append(poststore[key] == value)
        elif z3.is_string(value):
            assert not isinstance(poststore[key], Dict)
            constraints.append(poststore[key] == value)
        elif isinstance(value, z3.FuncDeclRef):
            postf = poststore[key]
            assert isinstance(postf, z3.FuncDeclRef)
            constraints.append(func_update(value, postf, fsupp.get(path, [])))
        else:
            postd = poststore[key]
            assert isinstance(postd, Dict)
            assert isinstance(value, Dict)
            constraints.extend(noup_cons(value, postd, fsupp, path))

    return constraints


def func_update(pref: z3.FuncDeclRef, postf: z3.FuncDeclRef, exc: List[List[Integer | Boolean | String]]) -> Boolean:
    """ construct forall quantified formula stating 'pref'=='postf' everywhere except on the 'exc' points"""
    
    fresh_vars = []
    assert pref.arity() == postf.arity(), "functions incompatible, different arities"
    for i in range(pref.arity()):
        assert pref.domain(i) == postf.domain(i), "functions incompatible, different domain types"
        if pref.domain(i) == z3.IntSort():
            fresh_vars.append(z3.FreshInt())
        elif pref.domain(i) == z3.BoolSort():
            fresh_vars.append(z3.FreshBool())
        elif pref.domain(i) == z3.StringSort():
            fresh_vars.append(z3.FreshConst(z3.StringSort()))
        else:
            assert False, "unsupported type" + pref.domain(i)

    conjuncts = []
    for elem in exc:
        equ = []
        for i in range(len(fresh_vars)):
            assert z3.is_int(elem[i]) == z3.is_int(fresh_vars[i]), "incompatible argument types"
            assert z3.is_bool(elem[i]) == z3.is_bool(fresh_vars[i]), "incompatible argument types"
            assert z3.is_string(elem[i]) == z3.is_string(fresh_vars[i]), "incompatible argument types"
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
    maybe_symvar = store[keys[0]]
    if len(keys) == 1:
        assert not isinstance(maybe_symvar, Dict), "contradicting types" 
        return maybe_symvar
    else:
        if isinstance(maybe_symvar, Dict):
            return walk_the_storage(maybe_symvar, keys[1:])
        else:
            assert False, "incompatible PreStore and keys list"

def to_label(history: List[str], name: str) -> str:
    label = ""

    for elem in history:
        label = label + elem + ";"

    label = label[:-1]
    label = label + "::" + name
    return label

def from_label(label: str) -> Tuple[List[str], str]:

    res = label.split(";")
    assert len(res) > 0
    name = res[-1].split("::")
    assert len(name) == 2
    hist = res[:-1] + [name[0]]

    return hist, name[1]

def to_storage_label(contract: str, name: str) -> str:
    return contract + "." + name

def to_node_name(case: List[Exp], initstore: SymStore)-> str:

    smt_case = [str(to_node_smt(elem)) for elem in case]
    name = ", ".join(smt_case)
    return name

def to_node_smt(exp: Exp)-> str:
    if isinstance(exp, Lit):
        return str(exp.value)
    
    elif isinstance(exp, Var): 
        return str(exp.name)
    
    elif isinstance(exp, EnvVar): 
        return str(exp.name)
       
    elif isinstance(exp, StorageItem):
        gen_storeloc = storageloc2node(exp.loc, exp.time) 
        return gen_storeloc
    
    # boolean expressions

    elif isinstance(exp, And):
        return "(" + to_node_smt(exp.left) + " and " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, Or):
        return "(" + to_node_smt(exp.left) + " or " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, Not):
        return  "not(" + to_node_smt(exp.value) + ")"
    
    elif isinstance(exp, Implies):
        return "(" + to_node_smt(exp.left) + " -> " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, ITE):
        return  "if " + to_node_smt(exp.condition) + \
                " then " + to_node_smt(exp.left) + \
                " else " + to_node_smt(exp.right)                        
    
    elif isinstance(exp, Eq):
        return "(" + to_node_smt(exp.left) + " = " +to_node_smt(exp.right) +")"

    elif isinstance(exp, Neq):
        return "(" + to_node_smt(exp.left) + " != " +to_node_smt(exp.right) +")"

    elif isinstance(exp, InRange):
        if isinstance(InRange.abitype, AbiIntType):
            ran = "int" + str(InRange.abitype.size)
        elif isinstance(InRange.abitype, AbiUIntType):
            ran = "uint" + str(InRange.abitype.size)
        elif isinstance(InRange.abitype, AbiAddressType):
            ran = "uint256"
        else:
            assert False
        return to_node_smt(exp.expr) + " inrange " + ran
    
    elif isinstance(exp, Lt):
        return "(" + to_node_smt(exp.left) + " < " + to_node_smt(exp.right) +")"

    elif isinstance(exp, Le):
        return "(" + to_node_smt(exp.left) + " <= " + to_node_smt(exp.right) +")"

    
    elif isinstance(exp, Ge):
        return "(" + to_node_smt(exp.left) + " >= " +to_node_smt(exp.right) +")"

    # integer expressions:
 
    elif isinstance(exp, Add):
        return "(" + to_node_smt(exp.left) + " + " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, Sub):
        return "(" + to_node_smt(exp.left) + " - " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, Mul):
        return "(" + to_node_smt(exp.left) + " * " +to_node_smt(exp.right) +")"
    
    elif isinstance(exp, Div):
        return "(" + to_node_smt(exp.left) + " / " +to_node_smt(exp.right) +")"

    
    elif isinstance(exp, Pow):
        return "(" + to_node_smt(exp.left) + " ** " +to_node_smt(exp.right) +")"

    else:
        assert False 

def storageloc2node(loc: StorageLoc, time: Timing) -> str:


        if time == Pre():
            pref = "pre("
        else:
            pref = "post("

        if isinstance(loc, VarLoc):
            return pref + loc.contract + "." + loc.name + ")"
        
        elif isinstance(loc, MappingLoc):
            smt_args = []
            for elem in loc.args:
                smt_args.append(to_node_smt(elem))
            func = storageloc2node(loc.loc, time)
            return pref + func + ")(" + ", ".join(smt_args) + ")" 
        
        else:
            assert isinstance(loc, ContractLoc)
            collect_list_of_keys = [loc.field]
            while not isinstance(loc.loc, VarLoc):
                loc = loc.loc
                if isinstance(loc, ContractLoc):
                    collect_list_of_keys = [loc.field] + collect_list_of_keys
                else:
                    assert False
            collect_list_of_keys = [loc.loc.contract, loc.loc.name] + collect_list_of_keys

            return pref+ ", ".join(collect_list_of_keys) + ")"

