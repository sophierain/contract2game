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
class AntiMap(StorageLoc):
    loc: StorageLoc
    loa: List[List[Exp]]

    def extend_loa(self, args: List[Exp]):
        assert args not in self.loa
        self.loa.append(args)

    def is_equiv(self, other: StorageLoc) -> bool:
        if not isinstance(other, AntiMap):
            return False
        if not self.loc.is_equiv(other.loc):
            return False
        if len(self.loa) != len(other.loa):
            return False
        for i in range(len(self.loa)):
            if len(self.loa[i]) != len(other.loa[i]):
                return False
            for j in range(len(self.loa[i])):
                if not self.loa[i][j].is_equiv(other.loa[i][j]):
                    return False
        return True

@dataclass
class TrackerElem:
    item: HistItem
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

            is_new = True
            for i in len(t_items):
                if isinstance(t_items[i].loc, AntiMap):
                    if func.is_equiv(t_items[i].loc.loc, []): 
                        # we have seen this mapping before and have to update the exception list loa
                        assert is_new == True
                        is_new = False
                        anti_elem = tracker[i] # found the trackerelem antimap of the current mapping loc
                        anti_elem.item.loc.extend_loa(item.loc.args) # extend exception list with current arguments
                        # this also extends tracker

            if is_new: # seeing this mapping for the first time
                antimap = AntiMap(func, [item.loc.args])
                anti_hist = HistItem(antimap, item.hist, item.type)
                if item.type == ActByteStr():
                    anti_elem = TrackerElem(anti_hist, Lit("", ActByteStr()), upstream)
                elif item.type == ActBool():
                    anti_elem = TrackerElem(anti_hist, Lit(False, ActBool()), upstream)
                else:
                    anti_elem = TrackerElem(anti_hist, Lit(0, ActInt()), upstream)
                tracker.append(anti_elem)

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
        # possibly a no update function constraint
        if isinstance(exp.left, HistItem):
            if isinstance(exp.left.loc, AntiMap):
                assert isinstance(exp.right, HistItem)
                assert isinstance(exp.right.loc, AntiMap)
                return func_update(exp.left, exp.right)
        
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
     

def apply_behaviour(tracker: Tracker,
                    history: List[str], 
                    contract_name: str, 
                    behv: Behavior)         -> Tuple[Tracker, List[Exp], List[Exp], List[Exp]]:

    prec = []
    updates = []
    case_cond = []

    name = history[-1]

    for exp in behv.caseConditions:
        case_cond.append(to_hist(history, exp))
  
    for exp in behv.preConditions:
        prec.append(to_hist(history, exp))

    # ignore post cond and inv for now

    for exp in behv.stateUpdates:
        updates.append(to_hist(history, exp))

    new_tracker = update_tracker(tracker, updates, name)
   
    no_update_constraints = no_update(new_tracker, history, contract_name, updates)

    return new_tracker, prec, updates + no_update_constraints, case_cond


def update_tracker(tracker: Tracker, updates: List[Exp], name: str) \
    -> Tracker:

    new_tracker = copy_update_tracker(tracker, name)

    for update in updates:
        assert isinstance(update, Eq)
        assert isinstance(update.left, HistItem)
        item = update.left
        value = update.right
        upstream = update.left.hist

        is_new = True # only applies to mappingloc and is true iff the args are seen the first time
        antielem_index = -1

        for i in range(len(new_tracker)):
            t_item = new_tracker[i].item
            if item.is_equiv(t_item):
                assert is_new
                is_new = False
                new_tracker[i] = TrackerElem(item, value, upstream)
            if isinstance(item.loc, MappingLoc):
                if isinstance(t_item.loc, AntiMap):
                    if t_item.loc.loc.is_equiv(item.loc.loc):
                        antielem_index = i
        
        if is_new:
            assert isinstance(item.loc, MappingLoc)
            assert antielem_index > -1
            # add new mapping instance to tracker 
            new_tracker.append(TrackerElem(item, value, upstream))
            # adapt loa and upstream of corresponding antimap
            anti_map = new_tracker[antielem_index].item.loc
            assert isinstance(anti_map, AntiMap)
            anti_map.extend_loa(item.loc.args)

    return new_tracker
    

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


def no_update(tracker: Tracker, updates: List[Exp]) -> List[Exp]:
    """Identifies all SymVars from poststore that are not assigned a new value in the updates contraints.
    Returns a list of constraints that assert the not-updated poststore Symvars have the same value as the 
    respective prestore symvars.
    Only add the constraints for the main contract, others irrelevant
    """

    noup_all = copy_tracker(tracker)
    noup = [elem.item for elem in noup_all]

    for update in updates:
        assert isinstance(update, Eq)
        item = update.left
        assert isinstance(item, HistItem)

        # search loc in tracker
        equi = False
        for elem in noup:
            if item.is_equiv(elem, tracker):
                assert equi == False
                equi = True
                noup.remove(elem)
        assert equi == True

    constraints = noup_cons(noup)

    return constraints


def noup_cons(noup: List[HistItem]) -> List[Exp]:

    constraints = []
    for elem in noup: 
        cons = Eq(elem, HistItem(elem.loc, elem.hist[-1], elem.type) )
        constraints.append(cons)

    return constraints


def func_update(left: HistItem, right: HistItem) -> Boolean:
    """ construct forall quantified formula stating 'pref'=='postf' everywhere except on the 'exc' points"""
    
    assert isinstance(left.loc, AntiMap)
    assert isinstance(right.loc, AntiMap)

    raw_exc = left.loc.loa
    assert len(raw_exc) > 0
    num_args = len(raw_exc[0])
    assert len(num_args) > 0
    assert all([num_args == len(elem) for elem in raw_exc]) #num args check
    assert all([ all([elem[i].type == raw_exc[0][i].type for elem in raw_exc])  for i in num_args]) #type check

    exc = []
    for args in raw_exc:
        exc.append([to_smt(elem) for elem in args])

    # convert left and right to z3.FuncDeclRef
    res_acttype = left.type
    arg_acttypes = [exp.type for exp in raw_exc[0]]

    # TO BE CONTINUED
    arg_types = []
    for elem in arg_acttypes:
        if elem == ActBool():
            arg_types.append(z3.BoolSort())
        elif elem == ActInt():
            arg_types.append(z3.IntSort())
        elif elem == ActByteStr():
            arg_types.append(z3.StringSort())
        else:
            assert False

    if res_acttype == ActBool():
        result = z3.BoolSort()
    elif res_acttype == ActInt():
        result = z3.IntSort()
    elif res_acttype == ActByteStr():
        result = z3.StringSort()
    else:
        assert False

    name_left = to_name(left.loc.loc)
    label_left = to_label(left.hist, name_left)
    func_left = z3.Function(label_left, *arg_types, result)

    name_right = to_name(right.loc.loc)
    label_right = to_label(right.hist, name_right)
    func_right = z3.Function(label_right, *arg_types, result)

    fresh_vars = []
    for sort in arg_types:
        if sort == z3.IntSort():
            fresh_vars.append(z3.FreshInt())
        elif sort == z3.BoolSort():
            fresh_vars.append(z3.FreshBool())
        elif sort == z3.StringSort():
            fresh_vars.append(z3.FreshConst(z3.StringSort()))
        else:
            assert False, "unsupported type" + sort

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
    rhs = func_left(*fresh_vars) == func_right(*fresh_vars)

    return z3.ForAll(fresh_vars, z3.Implies(lhs, rhs))



# "little" helper functions

def copy_tracker(tracker: Tracker) -> Tracker:
    pass

def copy_update_tracker(tracker: Tracker, name: str) -> Tracker:
    pass

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