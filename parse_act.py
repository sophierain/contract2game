from act_ast import *
from typing import Any, Dict, Iterable, List, Union

def parse_act_json(obj: Dict) -> Act:
    
    assert(obj["kind"]=="Program", "'kind' key does not match 'Program'")
    assert(obj["store"], "Missing 'store' key")
    assert(obj["contracts"], "Missing 'contracts' key")

    return Act(parse_store(obj["store"]), [parse_contract(elem) for elem in obj["contracts"]])


def parse_store(store: Dict) -> Storage:
    
    assert(store["kind"]=="Storages", "'kind' key does not match 'Storages'")
    assert(store["storages"], "Missing 'storages' key")

    return Storage(dict()) # TO DO

def parse_contract(contract: Dict) -> Contract:
    
    assert(contract["kind"]=="Contract", "'kind' key does not match 'Contract'")
    assert(contract["constructor"], "Missing 'constructor' key")
    assert(contract["behaviors"], "Missing 'behaviors' key")
    assert(contract["constructor"]["contract"], "Missing 'contract' key at 'contract['constructor']'")

    return Contract(contract["constructor"]["contract"], parse_constructor(contract["constructor"]), [parse_behavior(elem) for elem in contract["behaviors"]])



def parse_constructor(ctor: Dict)-> Constructor:
    
    assert(ctor["kind"]=="Constructor", "'kind' key does not match 'Constructor'")
    assert(ctor["initial_storage"], "Missing 'initial_storage' key")
    assert(ctor["interface"], "Missing 'interface' key")
    assert(ctor["invariants"], "Missing 'invariants' key")
    assert(ctor["preConditions"], "Missing 'preConditions' key")
    assert(ctor["postConditions"], "Missing 'postConditions' key")

    return Constructor(
                        parse_interface(ctor["interface"]),
                        [parse_boolexp(elem) for elem in ctor["initial_storage"] ],
                        [parse_boolexp(elem) for elem in ctor["preConditions"] ],
                        [parse_boolexp(elem) for elem in ctor["postConditions"] ],
                        [parse_boolexp(elem) for elem in ctor["invariants"] ]
                        )

def parse_behavior(behv: Dict) -> Behavior:
    
    # change Behaviour to Behavior
    assert(behv["kind"]=="Behaviour", "'kind' key does not match 'Behaviour'")
    assert(behv["name"], "Missing 'name' key")
    assert(behv["interface"], "Missing 'interface' key")
    assert(behv["case"], "Missing 'case' key")
    assert(behv["preConditions"], "Missing 'preConditions' key")
    assert(behv["postConditions"], "Missing 'postConditions' key")
    assert(behv["returns"], "Missing 'returns' key")
    assert(behv["stateUpdates"], "Missing 'stateUpdates' key")


    return Behavior(
                    behv["name"],
                    parse_interface(behv["interface"]),
                    [parse_boolexp(elem) for elem in behv["case"] ],
                    [parse_boolexp(elem) for elem in behv["preConditions"] ],
                    [parse_boolexp(elem) for elem in behv["postConditions"] ],
                    parse_exp(behv["returns"]),
                    [parse_stateupdate(elem) for elem in behv["stateUpdates"] ]
                    )

def parse_interface(interface: Dict) -> Interface:
    # change json structure; Dict rather than str
    return Interface("", []) # TO DO


# the following code expects all input to be dicts
# either a base case dict:
#   "literal": "x",
#   "type": 'int"
# or another base case dict:
#   "var": "x",
#   "type": "bool"
# or yet another base case dict:
#   "envValue": "x",
#   "type": "int" or "bool"
# or  for storageitems:
#   "entry": Dict,
#   "timing": "Pre" or "Post"
#
# or recursive case containing
#           "symbol": "<=",
#           "args": [...],
#           "type": "int"


# could be deleted as well
def parse_boolexp(boolexp: Dict) -> BoolExp:
    res = parse_exp(boolexp)
    assert(type(res)==BoolExp, "not a boolean expression")
    return res

def parse_intexp(intexp: Dict) -> IntExp:
    res = parse_exp(intexp)
    assert(type(res)==IntExp, "not an integer expression")
    return res


def parse_exp(exp: Dict) -> Exp:

    keys = exp.keys()
    if "symbol" in keys:
        #recursive case
        assert("type" in keys, "Missing 'type' key")    
        assert("args" in keys, "Missing 'args' key")

        return parse_symbol(exp["symbol"], exp["type"], [parse_exp(elem) for elem in exp["args"]])

    else:
        # Base Case
        if "literal" in keys:
            # Literal; either int or bool
            assert("type" in keys, "Missing 'type' key") 
            if exp["type"] == "int":
                return LitInt(int(exp["literal"]))
            elif exp["type"] == "bool":
                return LitBool(bool(exp["literal"]))
            else:
                assert(False, "unsupported literal type")

        elif "var" in keys:
            # Variable; either int or bool
            assert("type" in keys, "Missing 'type' key") 
            if exp["type"] == "int":
                return VarInt(exp["var"])
            elif exp["type"] == "bool":
                return VarBool(exp["var"])
            else:
                assert(False, "unsupported variable type")
    
        elif "envValue" in keys:
            # environment value; either int or bool
            assert("type" in keys, "Missing 'type' key") 
            if exp["type"] == "int":
                return EnvVarInt(exp["envValue"])
            elif exp["type"] == "bool":
                return EnvVarBool(exp["envValue"])
            else:
                assert(False, "unsupported environment variable type")

        elif "entry" in keys:
            # storage item; with timing either pre or post
            assert("timing" in keys, "Missing 'type' key")
            if exp["timing"] == "Pre":
                return StorageItem(parse_storageloc(exp["entry"]), Pre())
            elif exp["timing"] == "Post":
               return StorageItem(parse_storageloc(exp["entry"]), Post())
            else:
                assert(False, "unsupported timing value") 

        else:
            assert(False, "unknown expression")

def parse_stateupdate(update: Dict) -> BoolExp:
    pass

def parse_symbol(symbol: str, type: str, args: List[Exp])-> Exp:
    pass

def parse_storageloc(sloc: Dict) -> StorageLoc:

    if "symbol" in sloc.keys():
        # MappingLoc case:
        assert(sloc["symbol"]== "lookup", "symbol not supported")
        assert(sloc["args"], "Missing 'args' key")
        assert(len(sloc["args"])==2)
        return MappingLoc(parse_storageloc(sloc["args"][0]), [parse_exp(elem) for elem in sloc["args"][0]]) # in json currently not in the correct format (see lines 76-93)

    elif "var" in sloc.keys():
        # VarLoc case:
        pass

    elif "contractvar" in sloc.keys(): #what is the correct key to ask for?
        # ContractLoc case:
        pass

    else:
        assert(False, "unsupported storage location")


    