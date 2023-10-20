from typing import Union, Set, Dict, List, Any, Tuple
from dataclasses import dataclass
from parse_act import *
from act_ast import *
import z3

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

postint = z3.Function("postint", z3.IntSort(), z3.IntSort())
postbool = z3.Function("postbool", z3.BoolSort(), z3.BoolSort())


@dataclass
class SymState:
    storage: SymStore
    constraints: List[Boolean]


@dataclass
class Tree:
    """a non-leaf node with children"""
    state: SymState
    children: Dict[str, 'Tree']




def extract_constraints(behv: Behavior) -> List[Exp]:
    """Returns the constraints from a behavior that are relevant for the consruction of the game tree"""
    return behv.caseConditions + behv.preConditions + behv.stateUpdates


def apply_behaviour(state: SymState, history: List[str], contract_name: str, contr: Constructor, behv: Behavior) -> SymState:
    """apply behavior 'behv' to the state 'state'"""

    new_storage = gen_poststore(state.storage, behv.name)



    constraints = {}
    for exp in behv.caseConditions:
        constraints.add(to_smt(state.storage, new_storage, history + [behv.name], exp)) # to_smt has to be adapted, esp. storageloc fct
    for exp in behv.preConditions:
        constraints.add(to_smt(state.storage, new_storage, history + [behv.name], exp))
    for exp in behv.postConditions:
        constraints.add(to_smt(state.storage, new_storage, history + [behv.name], exp))
    for exp in contr.invariants:
        constraints.add(to_smt(state.storage, new_storage, history + [behv.name], exp))

    update_constraints = {}
    for exp in behv.stateUpdates:
        update_constraints = constraints.add(to_smt(state.storage, new_storage, history + [behv.name], exp))
   
    no_update_constraints = no_update(state.storage, new_storage, behv.name, behv.stateUpdates)

    return SymState(new_storage, constraints.union(update_constraints.union(no_update_constraints))) 

def no_update(prestore: SymStore, poststore: SymStore, history: List[str], updates: List[Exp]) -> List[Boolean]:
    """Identifies all SymVars from poststore that are not assigned a new value in the updates contraints.
    Returns a list of constraints that assert the not-updated poststore Symvars have the same value as the 
    respective prestore symvars.
    Only add the constraints for the main contract, others irrelevant
    """

    noup = copy_symstore(prestore)
    supp_fctargs = dict()

    for update in updates:
        assert isinstance(update, Eq)
        item = update.left
        assert isinstance(item, StorageItem)
        loc = item.loc

        # search loc in postStore
        if isinstance(loc, VarLoc):
            del noup[loc.contract][loc.name]
        elif isinstance(loc, MappingLoc):
            keys = []
            new_loc = loc.loc
            while isinstance(new_loc, ContractLoc):
                # contractloc case:
                keys = [new_loc.field] + keys
                new_loc = new_loc.loc
            #varloc case:
            assert isinstance(new_loc, VarLoc)
            keys = [new_loc.contract, new_loc.name] + keys
            if keys in supp_fctargs:
                supp_fctargs[keys].append([to_smt(prestore, poststore, history, elem) for elem in loc.args])
            else:
                supp_fctargs[keys] = [[to_smt(prestore, poststore, history, elem) for elem in loc.args]]
        else: 
            # contractloc case
            keys = []
            while isinstance(loc, ContractLoc):
                keys = [new_loc.field] + keys
                loc = loc.loc
            # reached varloc
            assert isinstance(new_loc, VarLoc)
            keys = [loc.contract, loc.name] + keys
            store = noup #shallow copy on purpose
            last_key = keys[-1]
            keys = keys[:-1]
            for elem in keys:
                store = store[elem]

            del store[last_key] # through call by reference noup was shrinked as intended

    constraints = []
    for key, value in noup:
        constraints.extend(noup_cons(value, poststore[key], supp_fctargs, [key]))

    return constraints

def noup_cons(prestore: PreStore,
              poststore: PreStore, 
              fsupp: Dict[ List[str],List[List[Integer | Boolean]]],
              path: List[str]
              )                                                    -> List[Boolean]:

    constraints = []
    for key, value in prestore:    
        if isinstance(value, Integer) or isinstance(value, Boolean):
            constraints.append(poststore[key] == value)
        elif isinstance(value, z3.FuncDeclRef):
            constraints.append(func_update(value, poststore[key], fsupp[path + [key]]))
        else:
            constraints.extend(noup_cons(value, poststore[key], fsupp, path + [key]))

    return constraints

def func_update(pref: z3.FuncDeclRef, postf: z3.FuncDeclRef, exc: List[List[Integer | Boolean]]) -> Boolean:
    """ construct forall quantified formula stating 'pref'=='postf' everywhere except on the 'exc' points"""
    pass


def copy_symstore(store: PreStore | SymStore) -> PreStore | SymStore:

    scopy = dict()
    for key, value in store.items():
        if isinstance(value, Dict):
            scopy[key] = copy_symstore(value)
        else: 
            scopy[key] = value

    return scopy


def gen_poststore(pre: Union[SymStore,PreStore], name: str) -> Union[SymStore,PreStore]:
    post = dict()

    for key, value in pre:
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


def reachable(state: SymState) -> z3.CheckSatResult:
    pass


def init_state(storage: Storage, ctor: Constructor, extraConstraints: Set[Exp]) -> SymState:
    """translate storage information to smt concepts, and collect initial constraints from user and invariants"""
    store: Dict = dict()
    for key, value in storage.items():
        store[key] = dict()
        for nested_key, nested_value in value.items():
            store[key][nested_key] = slottype2smt(key, nested_key, nested_value, storage)


    smt_constraints = []
    for exp in extraConstraints:
        smt_constraints.append(to_smt(store, [], exp))

    return SymState(store, smt_constraints)


def contract2tree(contract: Contract, storage: Storage) -> Tree:
    """ description to be added"""

    # to be extended with actual extra constraints!
    extra_constraints = {}
    root = init_state(storage, contract.constructor, extra_constraints)
    
    return generate_tree(Tree(root, dict()), [], contract.constructor, contract.behaviors)


def generate_tree(tree: Tree, history: List[str], contr: Constructor, behvs: List[Behavior]) -> Tree:
    """recursively extends the tree by applying all behaviors to all leaves until no new reachable states are found"""
    
    children = dict()
    for behv in behvs:
        children[behv.name] = apply_behaviour(tree.state, history, contr, behv)

    pass

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


def to_smt(store: SymStore, history: List[str], exp: Exp) -> Integer | Boolean:
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
        result = generate_smt_storageloc(store, history, exp.loc) # to be adapted!
        if isinstance(exp.time, Post): # cannot work this way
            if isinstance(exp.type, ActBool):
                return postbool(result)
            else:
                 return postint(result)
        else:
            return result
    
    # boolean expressions

    elif isinstance(exp, And):
        return z3.And(to_smt(store, history, exp.left),
                      to_smt(store, history, exp.right)
                      )
    
    elif isinstance(exp, Or):
        return z3.Or(to_smt(store, history, exp.left), 
                     to_smt(store, history, exp.right)
                     )
    
    elif isinstance(exp, Not):
        return z3.Not(to_smt(store, history, exp.value))
    
    elif isinstance(exp, Implies):
        return z3.Implies(to_smt(store, history, exp.left), 
                          to_smt(store, history, exp.right)
                          )
    
    elif isinstance(exp, ITE):
        return z3.If(to_smt(store, history, exp.condition),
                     to_smt(store, history, exp.left),
                     to_smt(store, history, exp.right)
                     )                   
    
    elif isinstance(exp, Eq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return to_smt(store, history, exp.left) == to_smt(store, history, exp.right)

    elif isinstance(exp, Neq):
        both_bool = isinstance(exp.left.type, ActBool) and isinstance(exp.right.type, ActBool)
        both_int = isinstance(exp.left.type, ActInt) and isinstance(exp.right.type, ActInt)
        assert both_bool or both_int, "left and right have to be of the same type"
        return z3.Not(to_smt(store, history, exp.left) == 
                      to_smt(store, history, exp.right))

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
                    to_smt(store, history, Le(min, exp.expr)),
                    to_smt(store, history, Le(exp.expr, max))
                    )
    
    elif isinstance(exp, Lt):
        return to_smt(store, history, exp.left) < \
               to_smt(store, history, exp.right)

    elif isinstance(exp, Le):
        return to_smt(store, history, exp.left) <= \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Gt):
        return to_smt(store, history, exp.left) > \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Ge):
        return to_smt(store, history, exp.left) >= \
               to_smt(store, history, exp.right)

    # integer expressions:
 
    elif isinstance(exp, Add):
        return to_smt(store, history, exp.left) + \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Sub):
        return to_smt(store, history, exp.left) - \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Mul):
        return to_smt(store, history, exp.left) * \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Div):
        return to_smt(store, history, exp.left) / \
               to_smt(store, history, exp.right)
    
    elif isinstance(exp, Pow):
        left = to_smt(store, history, exp.left)
        right = to_smt(store, history, exp.right)
        assert isinstance(left, int) & isinstance(right, int), "symbolic exponentiation not supported"
        return left ** right

    else:
        assert isinstance(exp, ITE)
        return z3.If(to_smt(store, history, exp.condition),
                    to_smt(store, history, exp.left),
                    to_smt(store, history, exp.right)) 
        

def generate_smt_storageloc(
                            store: SymStore, 
                            history: List[str], 
                            loc: StorageLoc)      ->     SymVar:
        """returns the correct smt variable from the SymStore"""
        if isinstance(loc, VarLoc):
            return store[loc.contract][loc.name]
        
        elif isinstance(loc, MappingLoc):
            smt_args = []
            for elem in loc.args:
                smt_args.append(to_smt(store, history, elem))

            func = generate_smt_storageloc(store, history, loc.loc)
            assert isinstance(func, z3.FuncDeclRef)
            return func(*smt_args)  # not convinced this works, should work though
        
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
        

def walk_the_storage(store: PreStore, keys: List) -> SymVar:
    
    isint = isinstance(store[keys[0]], int)
    isintsort = isinstance(store[keys[0]], z3.ArithRef)
    isbool = isinstance(store[keys[0]], bool)
    isboolsort = isinstance(store[keys[0]], z3.BoolRef)
    isfun = isinstance(store[keys[0]], z3.FuncDeclRef)
    issymvar = isfun or isint or isintsort or isbool or isboolsort
    if len(keys)==1:
        assert issymvar, "contradicting types" 
        return store[keys[0]]
    else:
        assert not issymvar, "contradicting types" 
        return walk_the_storage(store[keys[0]], keys[1:])

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


