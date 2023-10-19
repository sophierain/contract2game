from act_ast import *
from typing import Dict, List

def parse_act_json(obj: Dict) -> Act:
    # assert 'store' in obj, "message"
    assert obj["kind"]=="Program", "'kind' key does not match 'Program'"
    assert "store" in obj, "Missing 'store' key"
    assert "contracts" in obj, "Missing 'contracts' key"

    return Act(parse_store(obj["store"]), [parse_contract(elem) for elem in obj["contracts"]])


def parse_store(store: Dict) -> Storage:
    
    assert store["kind"]=="Storages", "'kind' key does not match 'Storages'"
    assert "storages" in store, "Missing 'storages' key"

    store_dict: Dict[str, Dict] = dict()

    for key, value in store.items():
        store_dict[key] = dict()
        for nested_key, nested_value in value.items():
            store_dict[key][nested_key] = parse_slottype(nested_value)

    return Storage(store_dict) 

def parse_slottype(input: List) -> SlotType:

    assert len(input)==2, "incorrect storage variable format"

    slottype = input[0]
    assert "kind" in slottype, "Missing 'kind' key"

    if slottype["kind"] == "ValueType":
        assert "valueType" in slottype, "Missing 'valueType' key"
        return parse_valuetype(slottype["valueType"])

    elif slottype["kind"] == "MappingType":
        assert "ixTypes" in slottype, "Missing 'ixTypes' key"
        assert "resType" in slottype, "Missing 'resType' key"
        return MappingType([parse_valuetype(elem) for elem in slottype["ixTypes"]], parse_valuetype(slottype["restype"]))
    
    else:
        assert False, "Unsupported slottype: " + slottype["kind"] 
        
def parse_valuetype(valuetype: Dict) -> ValueType:
    assert "kind" in valuetype,"Missing 'kind' key"

    if valuetype["kind"]== "ContractType":
        assert "name" in valuetype, "missing 'name' key"
        return ContractType(valuetype["name"])
    
    elif valuetype["kind"] == "AbiType":
        assert "abiType" in valuetype, "Missing 'abiType' key" 
        return parse_abitype(valuetype["abiType"])
    
    else:
        assert False, "Unsupported value type: " + valuetype["kind"]

def parse_abitype(abi: Dict) -> AbiType:
    assert "type" in abi, "Missing 'type' key"

    if abi["type"]== "UInt":
        assert "size" in abi, "Missing 'size' key"
        return AbiUIntType(int(abi["size"]))
    elif abi["type"]== "Int":
        assert "size" in abi, "Missing 'size' key"
        return AbiIntType(int(abi["size"]))
    elif abi["type"]== "Address":
        return AbiAddressType()
    elif abi["type"]== "Bool":
        return AbiBoolType()
    elif abi["type"]== "Bytes":
        assert "size" in abi, "Missing 'size' key"
        return AbiBytesType(int(abi["size"]))
    elif abi["type"]== "BytesDynamic":
        return AbiBytesDynamicType() 
    elif abi["type"]== "String":
        return AbiStringType() 
    elif abi["type"]== "ArrayDynamic":
        assert "arraytype" in abi, "Missing 'arraytype' key"
        return AbiArrayDynamicType(parse_abitype(abi["arraytype"]))
    elif abi["type"]== "Array":
        assert "size" in abi, "Missing 'size' key"
        assert "arraytype" in abi, "Missing 'arraytype' key"
        return AbiArrayType(int(abi["size"]), parse_abitype(abi["arraytype"]))
    elif abi["type"]== "Tuple":
        assert "elemTypes" in abi, "Missing 'elemTypes' key"
        return AbiTupleType([parse_abitype(elem) for elem in abi["elemTypes"]])
    elif abi["type"]== "Function":
        return AbiFunctionType()
    else:
        assert False, "Unsupported abi type: " + abi["type"]
    
    

def parse_contract(contract: Dict) -> Contract:
    
    assert contract["kind"]=="Contract", "'kind' key does not match 'Contract'"
    assert "constructor" in contract, "Missing 'constructor' key"
    assert "behaviors" in contract, "Missing 'behaviors' key"
    assert "contract" in contract["constructor"], "Missing 'contract' key at 'contract['constructor']'"

    return Contract(contract["constructor"]["contract"], parse_constructor(contract["constructor"]), [parse_behavior(elem) for elem in contract["behaviors"]])



def parse_constructor(ctor: Dict)-> Constructor:
    
    assert ctor["kind"]=="Constructor", "'kind' key does not match 'Constructor'"
    assert "initial_storage" in ctor, "Missing 'initial_storage' key"
    assert "interface" in ctor, "Missing 'interface' key"
    assert "invariants" in ctor, "Missing 'invariants' key"
    assert "preConditions" in ctor, "Missing 'preConditions' key"
    assert "postConditions" in ctor, "Missing 'postConditions' key"

    return Constructor(
                        parse_interface(ctor["interface"]),
                        [parse_initstore(elem) for elem in ctor["initial_storage"] ], 
                        [parse_boolexp(elem) for elem in ctor["preConditions"] ],
                        [parse_boolexp(elem) for elem in ctor["postConditions"] ],
                        [exp  for elem in ctor["invariants"] for exp in parse_invariants(elem)] 
                        )

def parse_behavior(behv: Dict) -> Behavior:
    # kind Behaviour
    assert behv["kind"]=="Behaviour", "'kind' key does not match 'Behaviour'"
    assert "name" in behv, "Missing 'name' key"
    assert "interface" in behv, "Missing 'interface' key"
    assert "case" in behv, "Missing 'case' key"
    assert "preConditions" in behv, "Missing 'preConditions' key"
    assert "postConditions" in behv, "Missing 'postConditions' key"
    assert "returns" in behv, "Missing 'returns' key"
    assert "stateUpdates" in behv, "Missing 'stateUpdates' key"


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
    assert "kind" in interface, "Missing 'kind' key"
    assert interface["kind"]=="Interface", "Unexpected 'kind': " + interface["kind"]+", expected 'Interface'"
    assert "id" in interface, "Missing 'id' key"
    assert "args" in interface, "Missing 'args' key"
    return Interface(interface["id"], [parse_decl(elem) for elem in interface["args"]])
                     
def parse_decl(decl: Dict) -> Decl:
    assert "kind" in decl, "Missing 'kind' key"
    assert decl["kind"]=="Declaration", "Unexpected 'kind': " + decl["kind"]+", expected 'Declaration'"
    assert "id" in decl, "Missing 'id' key"
    assert "abitype" in decl, "Missing 'abitype' key"
    return Decl(decl["id"], parse_abitype(decl["abitype"])) 

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



def parse_boolexp(boolexp: Dict) -> Exp:
    res = parse_exp(boolexp)
    assert res.type == ActBool, "not a boolean expression"
    return res

def parse_intexp(intexp: Dict) -> Exp:
    res = parse_exp(intexp)
    assert res.type == ActInt, "not an integer expression"
    return res

def parse_typedexp(texp: Dict) -> Exp:

    assert "type" in texp, "Missing 'type' key"    
    assert "expression" in texp, "Missing 'expression' key"
    
    if texp["type"] == "AInteger":
        return parse_intexp(texp["expression"])
    elif texp["type"] == "ABoolean":
        return parse_boolexp(texp["expression"])
    else:
        assert False, "Unsupported type: " + texp["type"]


def parse_exp(exp: Dict) -> Exp:

    keys = exp.keys()
    if "symbol" in keys:
        #recursive case
        assert "type" in keys, "Missing 'type' key"    
        assert "args" in keys, "Missing 'args' key"
        if exp["symbol"] == "inrange":
            assert len(exp["args"]) == 2, "two arguments expected for 'inrange'"
            first_arg = parse_exp(exp["args"][0])
            second_arg = parse_abitype(exp["args"][1])
            assert isinstance(first_arg.type, ActInt), "first argument expected to be an integer expression"
            assert isinstance(second_arg, AbiIntType) or isinstance(second_arg, AbiUIntType) or isinstance(second_arg, AbiAddressType), \
                    "second argument expected to be of abi type int, uint or address"
            return InRange(first_arg, second_arg)
        else:
            return parse_symbol(exp["symbol"], exp["type"], [parse_exp(elem) for elem in exp["args"]])

    else:
        # Base Case
        if "literal" in keys:
            # Literal; either int or bool
            assert "type" in keys, "Missing 'type' key" 
            if exp["type"] == "int":
                return Lit(int(exp["literal"]), ActInt())
            elif exp["type"] == "bool":
                return Lit(bool(exp["literal"]), ActBool())
            else:
                assert False, "unsupported literal type"

        elif "var" in keys:
            # Variable; either int or bool
            assert "type" in keys, "Missing 'type' key"
            if exp["type"] == "int":
                return Var(exp["var"], ActInt())
            elif exp["type"] == "bool":
                return Var(exp["var"], ActBool())
            else:
                assert False, "unsupported variable type"
    
        elif "envValue" in keys:
            # environment value; either int or bool
            assert "type" in keys, "Missing 'type' key" 
            if exp["type"] == "int":
                return EnvVar(exp["envValue"], ActInt())
            elif exp["type"] == "bool":
                return EnvVar(exp["envValue"], ActBool())
            else:
                assert False, "unsupported environment variable type"

        elif "entry" in keys:
            # storage item; with timing either pre or post
            assert "timing" in keys, "Missing 'timing' key"
            assert "type" in keys, "Missing 'type' key"
            if exp["timing"] == "Pre":
                if exp["type"] == "int":
                    return StorageItem(parse_storageloc(exp["entry"]), Pre(), ActInt())
                elif exp["type"] == "bool":
                    return StorageItem(parse_storageloc(exp["entry"]), Pre(), ActBool())
                else: 
                    assert False, "unsupported 'type' value" 
            elif exp["timing"] == "Post":
                if exp["type"] == "int":
                    return StorageItem(parse_storageloc(exp["entry"]), Post(), ActInt())
                elif exp["type"] == "bool":
                    return StorageItem(parse_storageloc(exp["entry"]), Post(), ActBool())
                else: 
                    assert False, "unsupported 'type' value" 
            else:
                assert False, "unsupported timing value" 

        else:
            assert False, "unknown expression"


def parse_storageloc(sloc: Dict) -> StorageLoc:

    assert "kind" in sloc, "Missing 'kind' key"

    if sloc["kind"] == "Mapping":
        assert "reference" in sloc, "Missing 'reference' key"
        assert "indexes" in sloc, "Missing 'indexes' key"
        return MappingLoc(parse_storageloc(sloc["reference"]), [parse_exp(elem) for elem in sloc["indexes"]])

    elif sloc["kind"] == "SVar":
        # VarLoc case:
        assert "svar" in sloc, "Missing 'svar' key"
        assert "contract" in sloc, "Missing 'contract' key"
        return VarLoc(sloc["contract"], sloc["svar"])

    elif sloc["kind"] == "Field": 
        # ContractLoc case:
        assert "reference" in sloc, "Missing 'reference' key"
        assert "field" in sloc, "Missing 'field' key"
        assert "contract"in sloc, "Missing 'contract' key"
        return ContractLoc(sloc["reference"] , sloc["contract"], sloc["field"])
    
    else:
        assert False, "unsupported storage kind: " + sloc["kind"]

def parse_symbol(symbol: str, type: str, args: List[Exp])-> Exp:    

        if symbol == "+":
            assert  len(args) == 2, "two arguments expected for +"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Add(*args)
        elif symbol == "-":
            assert len(args) == 2, "two arguments expected for -"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Sub(*args)
        elif symbol == "*":
            assert len(args) == 2, "two arguments expected for *"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Mul(*args)
        elif symbol == "/":
            assert len(args) == 2, "two arguments expected for /"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Div(*args)
        elif symbol == "^":
            assert len(args) == 2, "two arguments expected for ^"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Pow(*args)
       

        elif symbol == "ite":
            assert len(args) == 3, "three arguments expected for 'ite'"
            if type=="int":
                assert isinstance(args[0].type, ActBool),"expected boolean expression arguments"
                assert all(isinstance(elem.type, ActInt) for elem in args[1:]), "expected integer expression arguments" 
                return ITE(*args, ActInt())
            elif type == "bool":
                assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
                return ITE(*args, ActBool())
            else:
                assert False, "Unsupported 'ite' type: " +type

        elif symbol == "=/=":
            assert len(args) == 2, "two arguments expected for '=/='"
            all_bool = all(isinstance(elem.type, ActBool) for elem in args)
            all_int = all(isinstance(elem.type, ActInt) for elem in args)
            assert all_bool or all_int, "expected all boolean or all integer expression arguments" 
            return Neq(*args)
        elif symbol == "==":
            assert len(args) == 2, "two arguments expected for '=='"
            all_bool = all(isinstance(elem.type, ActBool) for elem in args)
            all_int = all(isinstance(elem.type, ActInt) for elem in args)
            assert all_bool or all_int, "expected all boolean or all integer expression arguments" 
            return Eq(*args)

        elif symbol == "and":
            assert len(args) == 2, "two arguments expected for 'and'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return And(*args)
        elif symbol == "or":
            assert len(args) == 2, "two arguments expected for 'or'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Or(*args)
        elif symbol == "not":
            assert len(args) == 1, "one argument expected for 'not'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Not(*args)
        elif symbol == "=>":
            assert len(args) == 2, "two arguments expected for '=>'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Implies(*args)

        elif symbol == "<":
            assert len(args) == 2, "two arguments expected for '<'"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Lt(*args)
        elif symbol == ">":
            assert len(args) == 2, "two arguments expected for '>'"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Gt(*args)
        elif symbol == "<=":
            assert len(args) == 2, "two arguments expected for '<='"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Le(*args)
        elif symbol == ">=":
            assert len(args) == 2, "two arguments expected for '>='"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Ge(*args)
        else:
            assert False, "Unsupported symbol: " + symbol

# remove constant 'blocks' from json, 
# rewrites are thus the only remaining stateupdates and hence the word rewrite can go away
# expect:
#   "location": StorageLocation
#   "value": Expression
# build an equality constraint:
#   post of location = value
# hence this is storageItem with loc=location

def parse_stateupdate(update: Dict) -> Exp:

    assert "location" in update, "Missing 'location' key"    
    assert "value" in update, "Missing 'value' key"  
    assert "type" in update["location"]  , "Missing 'type' key"

    if update["location"]["type"]== "int": 
        return Eq(
                StorageItem(
                    parse_storageloc(update["location"]), 
                    Post(),
                    ActInt()
                ), 
                parse_exp(update["value"])
                )
    elif update["location"]["type"]== "bool":
        return Eq(
                StorageItem(
                    parse_storageloc(update["location"]), 
                    Post(),
                    ActBool()
                ), 
                parse_exp(update["value"])
                )
    else: 
        assert False, "unsupported StorageItem type: " + update["location"]["type"]

def parse_initstore(initstore: Dict) ->  Exp:    
    assert "location" in initstore, "Missing 'location' key"    
    assert "value" in initstore, "Missing 'value' key"  
    assert "type" in initstore["location"]  , "Missing 'type' key"

    if initstore["location"]["type"]== "int": 
        return Eq(
                StorageItem(
                    parse_storageloc(initstore["location"]), 
                    Pre(),
                    ActInt()
                ), 
                parse_exp(initstore["value"])
                )
    elif initstore["location"]["type"]== "bool":
        return Eq(
                StorageItem(
                    parse_storageloc(initstore["location"]), 
                    Pre(),
                    ActBool()
                ), 
                parse_exp(initstore["value"])
                )
    else: 
        assert False, "unsupported StorageItem type: " + initstore["location"]["type"]

def parse_invariants(inv: Dict) -> List[Exp]:
    assert "kind" in inv, "Missing 'kind' key"    
    assert inv["kind"]=="Invariant", "not of kind invariant"  
    assert "predicate" in inv, "Missing 'predicate' key"

    return [parse_exp(elem) for elem in inv["predicate"] ]

