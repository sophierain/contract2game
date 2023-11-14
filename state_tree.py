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

Upstream = List[str]
PreStore = Dict[str, Union[Tuple[SymVar, SymVar, List[Upstream]], 'PreStore']]
SymStore = Dict[str, PreStore]       
"""
x = z3.Int(<name>): z3.ArithRef                                         integer constant named <name>
z = z3.Bool(<name>): z3.BoolRef   
s = z3.String(<name>): z3.SeqRef                                                  boolean constant named <name>
y = z3.Function(<fct_name>, <z3 input sort(s)>, <z3 ouput sort>): z3.FuncDeclRef   uninterpreted function named <fct_name>
"""

@dataclass
class AntiMap:
    loc: StorageLoc
    loa: List[List[Exp]]
    hist: List[str]
    type: ActType

    def extend_loa(self, args: List[Exp]):
        assert args not in self.loa
        self.loa.append(args)

@dataclass
class TrackerElem:
    item: Union[HistItem, AntiMap]
    value: Exp
    upstream: List[str]

Tracker = List[TrackerElem]

@dataclass
class Tree:
    """a node with possibly 0 children"""
    tracker: Tracker
    beh_case: List[Exp]
    preconditions: List[Exp]
    updates: List[Exp]
    split_constraints: List[Exp] # are actually new case conditions
    children: Dict[str, 'Tree']

    def __repr__(self, level = 0) -> str:  # to be adapted
        
        indent = "   "*level
        res = f"{indent}State: \n"
        res = res + f"{indent}   Storage:\n"
        for key, value in self.store.items():
            res = res + f"      {indent}{key}: {value}\n"
        res = res + f"{indent}   Case:\n"
        for elem in self.beh_case:
            res = res + f"{indent}      {elem}\n"
        res = res + f"{indent}   Preconditions:\n"
        for elem in self.preconditions:
            res = res + f"{indent}      {elem}\n"
        res = res + f"{indent}   Updates:\n"
        for elem in self.updates:
            res = res + f"{indent}      {elem}\n"
        res = res + f"{indent}   Split Constraints:\n"
        for elem in self.split_constraints:
            res = res + f"{indent}      {elem}\n"
        res = res + f"{indent}Children:\n"
        for ckey, cvalue in self.children.items():
            res = res + f"{indent}   {ckey}:\n{cvalue.__repr__(level + 1)}\n"

        return res

    def structure(self, level: int = 0):
        for key, value in self.children.items():
                print(level*"   " + key)
                value.structure(level + 1)
        return


# main functions

def contract2tree(contract: Contract, extra_constraints: List[Exp]) -> Tree:
    """ 
    contract: contract to be analyzed
    storage: storage dict of contract, contains all variables to be considered
    extra_constraints: a list of user defined constraints to be enforced as preconditions

    returns: a tree containg all possible sequential executions of the different behaviors of the contract
    
    """

    init_tracker, init_prec, init_updates = init_state(contract.constructor, extra_constraints)
    
    return generate_tree([to_bool(exp) for exp in init_prec + init_updates], init_tracker, init_prec, init_updates, [], [],  \
                          contract.name, contract.constructor, contract.behaviors)


def init_state(ctor: Constructor, extraConstraints: List[Exp]) -> Tuple[Tracker, List[Exp], List[Exp]]:
    """
    storage: storage dict of contract, contains all variables to be considered
    ctor: constructor of the contract, might be used later
    extra_constraints: a list of user defined constraints to be enforced as preconditions List[Boolean]

    returns: all ingredients to create the root of a tree containing translated storage information to smt concepts, 
             and collected initial constraints from user
    
    """
    prec = []
    updates = []

    for exp in ctor.initial_storage:
        updates.append(to_hist([], exp))

    for exp in extraConstraints:
        prec.append(to_hist([], exp))

    tracker = init_tracker(updates)

    return tracker, prec, updates


def init_tracker(updates: List[Exp]) -> Tracker:
    tracker: Tracker = []

    for elem in updates:
        assert isinstance(elem, Eq)
        assert isinstance(elem.left, HistItem)
        assert elem.left.hist == []

        item = elem.left

        value = elem.right

        upstream = []

        telem = TrackerElem(item, value, upstream)
        tracker.append(telem)

        if isinstance(item.loc, MappingLoc): # checking if we have seen this mapping before
            t_items = [elem.item for elem in tracker]
            func = item.loc.loc
            is_new = [key.loc == func and isinstance(key, AntiMap) for key in t_items]

            if not any(is_new): # seeing this mapping for the first time
                antimap = AntiMap(func, [item.loc.args], item.hist, item.type)
                if item.type == ActByteStr():
                    anti_elem = TrackerElem(antimap, Lit("", ActByteStr()), upstream)
                elif item.type == ActBool():
                    anti_elem = TrackerElem(antimap, Lit(False, ActBool()), upstream)
                else:
                    anti_elem = TrackerElem(antimap, Lit(0, ActInt()), upstream)
                tracker.append(anti_elem)

            else: 
                # we have seen this mapping before and have to update the exception list loa
                assert is_new.count(True) == 1
                ind = is_new.index(True)
                anti_elem = tracker[ind] # found the trackerelem antimap of the current mapping loc
                anti_elem.item.extend_loa(item.loc.args) # extend exception list with current arguments
                # this also extends tracker

    return tracker
    

def to_hist(hist: List[str], exp: Exp) -> Exp:
    '''
    converts StorageItems to HistItems, Var to histvar and envvvar to histenvvar
    with the given (post)history hist
    '''

    non_cnf = isinstance(exp, Implies) or isinstance(exp, InRange)

    assert not non_cnf, "to_cnf to be called first"
    
    if isinstance(exp, StorageItem): 
        if exp.time == Pre():
            item_hist = hist[-1]
        else: 
            item_hist = hist

        if isinstance(exp.loc, MappingLoc):
            exp_loc = MappingLoc(exp.loc.loc, [to_hist(hist, arg) for arg in exp.loc.args])
        else:
            exp_loc = exp.loc
        
        return HistItem(exp_loc, item_hist, exp.type)
    
    elif  isinstance(exp, Var):
        return HistVar(exp.name, hist, type)
    
    elif  isinstance(exp, EnvVar):
        return HistEnvVar(exp.name, hist, type)
    
    elif isinstance(exp, Lit):
        return exp
    elif isinstance(exp, And):
        return And(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Or):
        return Or(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Not):
        return Not(to_hist(hist, exp.value), exp.type)
    elif isinstance(exp, ITE):
        return ITE(to_hist(exp.condition), to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Eq):
        return Eq(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Neq):
        return Neq(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Add):
        return Add(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Sub):
        return Sub(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Mul):
        return Mul(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Div):
        return Div(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Pow):
        return Pow(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Lt):
        return Lt(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Le):
        return Le(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Gt):
        return Gt(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    elif isinstance(exp, Ge):
        return Ge(to_hist(hist, exp.left), to_hist(hist, exp.right), exp.type)
    else:
        assert False


def generate_tree(
                  constraints: List[Boolean], 
                  tracker: Tracker,
                  prec: List[Exp],
                  updates: List[Exp],
                  case_cond: List[Exp], 
                  history: List[str], 
                  contract_name: str, 
                  contr: Constructor, 
                  behvs: List[Behavior])             -> Tree:
    """
    recursively extends the tree by applying all behaviors to all leaves 
    until no new reachable states are found
    """

    children_solver = z3.Solver()
    
    children: Dict[str, Tree] = dict()
    for behv in behvs:
        child_name = behv.name + "__" + to_node_name(behv.caseConditions)
        # naive breaking condition: no 2 functions (behavior) can be called twice
        if not child_name in history:
            # apply behaviour already returns the hist versions of vars and storage
            child_tracker, child_prec, child_updates, child_case = \
                  apply_behaviour(tracker, history + [child_name], contract_name, contr, behv)
            child_constraints = [to_bool(exp) for exp in child_prec + child_updates + child_case]
            reachable = children_solver.check(constraints + child_constraints)
            if reachable == z3.sat:
                children[child_name] = generate_tree(constraints + child_constraints, 
                                                    child_tracker,
                                                    child_prec,
                                                    child_updates,
                                                    child_case,
                                                    history + [child_name],
                                                    contract_name,
                                                    contr, 
                                                    behvs)
            elif reachable == z3.unknown:
                logging.info("solver returned 'unkown'")
                assert False
        
    return Tree(tracker, case_cond, prec, updates, [], children)


# maybe obsolete
def slottype2smt(contract: str, name: str, slot: SlotType, storage: Storage, init_values: List[Exp]) \
                                                                                -> SymVar | PreStore :
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
        assert slot.contract in storage 
        #repeat stuff with storage[slot.contract] and add contract to the storage label
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


def to_bool(exp: Exp) -> Boolean:
    res = to_smt(exp)
    assert isinstance(res, bool) or isinstance(res, z3.BoolRef), "boolean expression expected"
    return res


def to_int(exp: Exp) -> Integer:
    res = to_smt(exp)
    assert isinstance(res, int) or isinstance(res, z3.ArithRef), "integer expression expected"
    return res


def to_smt( exp: Exp) -> Integer | Boolean | String:
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

    nothistversions = isinstance(exp, Var) or isinstance(exp, EnvVar) \
                                           or isinstance(exp, StorageItem)
    assert not nothistversions, "to_hist to be called before to_smt"

    assert not isinstance(exp, Implies) and not isinstance(exp, InRange), \
                                            "to_cnf to be called before to_smt"

    if isinstance(exp, Lit):
        return exp.value
    
    elif isinstance(exp, HistVar): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(exp.hist, exp.name))
        elif isinstance(exp.type, ActByteStr):
            return z3.String(to_label(exp.hist, exp.name))
        else:
            return z3.Int(to_label(exp.hist, exp.name))
    
    elif isinstance(exp, HistEnvVar): 
        if isinstance(exp.type, ActBool):
            return z3.Bool(to_label(exp.hist, exp.name))
        elif isinstance(exp.type, ActByteStr):
            return z3.String(to_label(exp.hist, exp.name))
        else:
            return z3.Int(to_label(exp.hist, exp.name))
       
    elif isinstance(exp, HistItem):
        gen_storeloc = generate_smt_storageloc(exp.hist, exp.loc, exp.type) 
        assert not isinstance(gen_storeloc, z3.FuncDeclRef)
        return gen_storeloc
    
    # boolean expressions

    elif isinstance(exp, And):
        return z3.And(to_bool(exp.left),
                      to_bool(exp.right)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(to_bool(exp.left), 
                     to_bool(exp.right)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(to_bool(exp.value))
    
    elif isinstance(exp, ITE):
        return z3.If(to_bool(exp.condition),
                     to_smt(exp.left),
                     to_smt(exp.right)
                     )                   
    
    elif isinstance(exp, Eq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        both_bytestr = isinstance(exp.left.type, ActByteStr) and isinstance(exp.right.type, ActByteStr)
        assert both_bool or both_int or both_bytestr, "left and right have to be of the same type"
        return to_smt(exp.left) == to_smt(exp.right)

    elif isinstance(exp, Neq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        both_bytestr = isinstance(exp.left.type, ActByteStr) and isinstance(exp.right.type, ActByteStr)
        assert both_bool or both_int or both_bytestr, "left and right have to be of the same type"
        return z3.Not(to_smt(exp.left) == 
                      to_smt(exp.right))
    
    elif isinstance(exp, Lt):
        return to_int(exp.left) < \
               to_int(exp.right)

    elif isinstance(exp, Le):
        return to_int(exp.left) <= \
               to_int(exp.right)
    
    elif isinstance(exp, Gt):
        return to_int(exp.left) > \
               to_int(exp.right)
    
    elif isinstance(exp, Ge):
        return to_int(exp.left) >= \
               to_int(exp.right)

    # integer expressions:
 
    elif isinstance(exp, Add):
        return to_int(exp.left) + \
               to_int(exp.right)
    
    elif isinstance(exp, Sub):
        return to_int(exp.left) - \
               to_int(exp.right)
    
    elif isinstance(exp, Mul):
        return to_int(exp.left) * \
               to_int(exp.right)
    
    elif isinstance(exp, Div):
        nom = to_int(exp.left)
        div = to_int(exp.left)
        if type(nom) == int and type(div) == int:
            return int(nom / div)
        else:
            res = nom / div
            assert isinstance(res, z3.ArithRef)
            return res

    
    elif isinstance(exp, Pow):
        left = to_int(exp.left)
        right = to_int(exp.right)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        assert False 
     

def apply_behaviour(store: SymStore,
                    history: List[str], 
                    contract_name: str, 
                    contr: Constructor,
                    behv: Behavior)         -> Tuple[SymStore, List[Boolean], List[Boolean], List[Boolean]]:

    new_storage = dict()
    for key, value in store.items():
        new_storage[key] = gen_poststore(value, history[-1])
    

    prec = []
    updates = []
    case_cond = []

    for exp in behv.caseConditions:
        case_cond.append(to_bool(store, new_storage, history, exp))
  
    for exp in behv.preConditions:
        prec.append(to_bool(store, new_storage, history, exp))

    # ignore post cond and inv for now

    # for exp in behv.postConditions:
    #     constraints.append(to_bool(store, new_storage, history, exp))
    # for exp in contr.invariants:
    #     constraints.append(to_bool(store, new_storage, history, exp))

    for exp in behv.stateUpdates:
        updates.append(to_bool(store, new_storage, history, exp))
   
    no_update_constraints = no_update(store, new_storage, history, contract_name, behv.stateUpdates)

    return new_storage, prec, updates + no_update_constraints, case_cond


def generate_smt_storageloc(
                            history: List[str], 
                            loc: StorageLoc,
                            type: ActType)      ->     SymVar:
    """returns the correct smt variable from the SymStore"""

    if isinstance(loc, VarLoc):
        var = to_name(loc)
        var = to_label(history, var)
        if type == ActInt():
            return z3.Int(var)
        elif type == ActBool():
            return z3.Bool(var)
        else:
            return z3.String(var)

    elif isinstance(loc, MappingLoc):
        smt_args = []
        arg_types = []
        for elem in loc.args:
            smt_args.append(to_smt(elem))

            if elem.type == ActBool():
                arg_types.append(z3.BoolSort())
            elif elem.type == ActInt():
                arg_types.append(z3.IntSort())
            elif elem.type == ActByteStr():
                arg_types.append(z3.StringSort())
            else:
                assert False

        if type == ActBool():
            result = z3.BoolSort()
        elif type == ActInt():
            result = z3.IntSort()
        elif type == ActByteStr():
            result = z3.StringSort()
        else:
            assert False

        fun_name = to_name(loc)
        fun_name = to_label(history, fun_name)
        func = z3.Function(fun_name, *smt_args, result)
        return func(*smt_args) 
    
    else:
        assert isinstance(loc, ContractLoc)
        var = to_name(loc)
        var = to_label(history, var)

        if type == ActInt():
            return z3.Int(var)
        elif type == ActBool():
            return z3.Bool(var)
        else:
            return z3.String(var)


# might be obsolete
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
        scopy[key] = (copy_prestore(value)[0], copy_prestore(value)[1], copy_prestore(value)[2]) # to be double checked

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

def to_node_name(case: List[Exp])-> str:

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

def to_name(pref: List[str], loc: StorageLoc) -> str:
    assert not isinstance(loc, MappingLoc)
    if isinstance(loc, VarLoc):
        return to_storage_label(loc.contract, loc.name)
    else: 
        return to_storage_label(to_name(loc.loc), loc.field)