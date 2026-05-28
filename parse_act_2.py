from act_ast import *
from typing import Dict, List

def parse_act_json(obj: Dict) -> Act:
    assert obj["kind"]=="Act", "'kind' key does not match 'Act'"
    assert "store" in obj, "Missing 'store' key"
    assert "contracts" in obj, "Missing 'contracts' key"

    return Act(parse_store(obj["store"]), [parse_contract(elem) for elem in obj["contracts"]])


def parse_store(store: Dict) -> Storage:
    
    assert store["kind"]=="Storages", "'kind' key does not match 'Storages'"
    assert "storages" in store, "Missing 'storages' key"

    store_dict: Dict[str, Dict] = dict()

    for contract_name, storage in store["storages"].items():
        store_dict[contract_name] = dict()
        if isinstance(storage, Dict):       
            for storage_name, storage_data in storage.items():
                store_dict[contract_name][storage_name] = parse_slottype(storage_data)

    return store_dict


def parse_slottype(input_storage_data: List) -> SlotType:

    assert len(input_storage_data)==2, "incorrect storage variable format"
    assert "type" in input_storage_data[0], "Missing 'type' key in storage variable definition"

    t = input_storage_data[0]
    return parse_type(t)

     
def parse_type(type_info: Dict) -> SlotType:  

    if type_info["type"]== "UInt":
        assert "size" in type_info, "Missing 'size' key"
        return AbiUIntType(int(type_info["size"]))
    elif type_info["type"]== "Int":
        assert "size" in type_info, "Missing 'size' key"
        return AbiIntType(int(type_info["size"]))
    elif type_info["type"]== "Address":
        return AbiAddressType()
    elif type_info["type"]== "Bool":
        return AbiBoolType()
    elif type_info["type"]== "Bytes":
        assert "size" in type_info, "Missing 'size' key"
        return AbiBytesType(int(type_info["size"]))
    elif type_info["type"]== "BytesDynamic":
        return AbiBytesDynamicType() 
    elif type_info["type"]== "String":
        return AbiStringType() 
    elif type_info["type"]== "ArrayDynamic":
        assert "arraytype" in type_info, "Missing 'arraytype' key"
        return AbiArrayDynamicType(parse_abitype(type_info["arraytype"]))
    elif type_info["type"]== "Array":
        assert "size" in type_info, "Missing 'size' key"
        assert "arraytype" in type_info, "Missing 'arraytype' key"
        return AbiArrayType(int(type_info["size"]), parse_abitype(type_info["arraytype"]))
    elif type_info["type"]== "Tuple":
        assert "elemTypes" in type_info, "Missing 'elemTypes' key"
        return AbiTupleType([parse_abitype(elem) for elem in type_info["elemTypes"]])
    elif type_info["type"]== "Function":
        return AbiFunctionType()

    elif type_info["type"]== "Contract":
        assert "name" in type_info, "missing 'name' key"
        return ContractType(type_info["name"])
    
    elif type_info["type"]== "Mapping":
        assert "keyType" in type_info, "Missing 'keyType' key"
        assert "valueType" in type_info, "Missing 'valueType' key"

        def coerce_to_ValueType(slot_type: SlotType) -> ValueType:
            if isinstance(slot_type, AbiUIntType):
                return AbiUIntType(slot_type.size)
            elif isinstance(slot_type, AbiIntType):
                return AbiIntType(slot_type.size)
            elif isinstance(slot_type, AbiAddressType):
                return AbiAddressType()
            elif isinstance(slot_type, AbiBoolType):
                return AbiBoolType()
            elif isinstance(slot_type, AbiBytesType):
                return AbiBytesType(slot_type.size)
            elif isinstance(slot_type, AbiBytesDynamicType):
                return AbiBytesDynamicType() 
            elif isinstance(slot_type, AbiStringType):
                return AbiStringType() 
            else:
                assert False, "unsupported or unexpected slot type: " + str(slot_type)
        return MappingType([coerce_to_ValueType(parse_type(type_info["keyType"]))], coerce_to_ValueType(parse_type(type_info["valueType"])))
    
    else:
        assert False, "Unsupported slottype: " + type_info["type"] 

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
    assert "behaviours" in contract, "Missing 'behaviours' key"
    assert "contract" in contract["constructor"], "Missing 'contract' key at 'contract['constructor']'"

    behvs = []
    for elem in contract["behaviours"]:
        behvs.extend(parse_behavior(elem))

    return Contract(contract["constructor"]["contract"], parse_constructor(contract["constructor"]), behvs)


def parse_constructor(ctor: Dict)-> Constructor:
    
    assert ctor["kind"]=="Constructor", "'kind' key does not match 'Constructor'"
    assert "cases" in ctor, "Missing 'cases' key"
    assert "interface" in ctor, "Missing 'interface' key"
    assert "invariants" in ctor, "Missing 'invariants' key"
    assert "preConditions" in ctor, "Missing 'preConditions' key"
    assert "postConditions" in ctor, "Missing 'postConditions' key"
    return Constructor(
                        parse_interface(ctor["interface"], ctor["contract"]),
                        [parse_constructor_case(elem) for elem in ctor["cases"][0]["body"] ], 
                        [parse_boolexp(elem) for elem in ctor["preConditions"] ],
                        [parse_boolexp(elem) for elem in ctor["postConditions"] ],
                        [exp  for elem in ctor["invariants"] for exp in parse_invariants(elem)] 
                        )

def parse_behavior_case(behv_case: Dict, name, interface, preconditions, postconditions) -> Behavior:
    assert "body" in behv_case, "Missing 'body' key"
    assert "caseCondition" in behv_case, "Missing 'caseCondition' key"

    case_condition = parse_boolexp(behv_case["caseCondition"])
    update = []

    for elem in behv_case["body"][0]:
        if "location" in elem:
            update.append(parse_stateupdate(elem))
        else:
            assert False, "unknown state update type in behavior case body: " + str(elem)

    if behv_case["body"][1] is not None:
        ret_parsed = parse_exp(behv_case["body"][1])
    else:
        ret_parsed = None

    return Behavior(
                name,
                parse_interface(interface, name),
                [case_condition],
                [parse_boolexp(elem) for elem in preconditions ],
                [parse_boolexp(elem) for elem in postconditions ],
                ret_parsed,
                update
                )


def parse_behavior(behv: Dict) -> List[Behavior]:
    assert behv["kind"]=="Behaviour", "'kind' key does not match 'Behaviour'"
    assert "name" in behv, "Missing 'name' key"
    assert "interface" in behv, "Missing 'interface' key"
    assert "cases" in behv, "Missing 'cases' key"
    assert "preConditions" in behv, "Missing 'preConditions' key"
    assert "postConditions" in behv, "Missing 'postConditions' key"

    behvs = []
    for case in behv["cases"]:
        behvs.append(parse_behavior_case(case, behv["name"], behv["interface"], behv["preConditions"], behv["postConditions"]))
        

    return behvs


def parse_interface(interface: Dict, contract: str) -> Interface:
    assert "kind" in interface, "Missing 'kind' key"
    assert interface["kind"]=="Interface", "Unexpected 'kind': " + interface["kind"]+", expected 'Interface'"
    assert "id" in interface, "Missing 'id' key"
    assert "args" in interface, "Missing 'args' key"
    return Interface(contract, [parse_decl(elem) for elem in interface["args"]])


def parse_decl(decl: Dict) -> Decl:
    assert "kind" in decl, "Missing 'kind' key"
    assert decl["kind"]=="Declaration", "Unexpected 'kind': " + decl["kind"]+", expected 'Declaration'"
    assert "id" in decl, "Missing 'id' key"
    assert "abitype" in decl, "Missing 'abitype' key"
    assert decl["id"][0] == "\""
    assert decl["id"][-1] == "\""
    return Decl(decl["id"][1:-1], parse_abitype(decl["abitype"]["abitype"])) 


def parse_boolexp(boolexp: Dict) -> Exp:
    res = parse_exp(boolexp, ActBool())
    assert res.type == ActBool(), "not a boolean expression"
    return res


def parse_intexp(intexp: Dict) -> Exp:
    res = parse_exp(intexp)
    assert res.type == ActInt(), "not an integer expression"
    return res


def parse_exp(exp: Dict, svartype = ActInt()) -> Exp:
    # print(exp)
    # print(type(exp))
    keys = exp.keys()
    if "symbol" in keys:
        #recursive case  
        assert "args" in keys, "Missing 'args' key"
        if exp["symbol"] == "inrange":
            assert len(exp["args"]) == 2, "two arguments expected for 'inrange'"
            expr_arg = parse_exp(exp["args"][1])
            type_arg = parse_abitype(exp["args"][0])
            # assert isinstance(expr_arg.type, ActInt) or isinstance(expr_arg.type, AbiAddressType), "expr argument expected to be an integer expression"
            # assert isinstance(type_arg, AbiIntType) or isinstance(type_arg, AbiUIntType) or isinstance(type_arg, AbiAddressType), \
            #         "second argument expected to be of abi type int, uint or address"
            return InRange(expr_arg, type_arg)
        else:
            return parse_symbol(exp["symbol"], [parse_exp(elem) for elem in exp["args"]])

    else:
        # Base Case
        if "literal" in keys:
            # Literal; either int, bool or bytestring
            assert "type" in keys, "Missing 'type' key" 
            if exp["type"] == "int":
                return Lit(int(exp["literal"]), ActInt())
            elif exp["type"] == "bool":
                if exp["literal"] == "False":
                    return Lit(False, ActBool())
                elif exp["literal"] == "True":
                    return Lit(True, ActBool())
                else:
                    assert False, "boolean neither False nor True but: " + exp["literal"]
            elif exp["type"] == "bytestring":
                return Lit(str(exp["literal"]), ActByteStr())
            else:
                assert False, "unsupported literal type"

        elif "var" in keys:
            # Variable; either int or bool
            if "svar" in exp["var"].keys():
                # storage variable
                assert "contract" in exp["var"], "Missing 'contract' key"
                assert "svar" in exp["var"], "Missing 'svar' key"
                assert "time" in exp["var"], "Missing 'time' key"
                print("storage item parsed:", StorageItem(VarLoc(exp["var"]["contract"], exp["var"]["svar"]), exp["var"]["time"], svartype))
                return StorageItem(VarLoc(exp["var"]["contract"], exp["var"]["svar"]), exp["var"]["time"], svartype) # type of storage item is not known at this point, will be filled in later
            elif "var" in exp["var"].keys():
                # local variable
                assert "abitype" in exp["var"].keys(), "Missing 'abitype' key"
                t = exp["var"]["abitype"]["abitype"]
                t_parsed = parse_abitype(t)
                return Var(exp["var"]["var"], t_parsed)
            else:
                assert False, "unknown variable type"
    
        elif "envValue"  in keys or "ethEnv" in keys:
            # environment value; int, bool or bytestring
            assert "type" in keys, "Missing 'type' key"
            if "envValue" in keys:
                key = "envValue"
            else:
                key = "ethEnv"
            if exp["type"] == "int":
                return EnvVar(exp[key], ActInt())
            elif exp["type"] == "bool":
                return EnvVar(exp[key], ActBool())
            elif exp["type"] == "bytestring":
                return EnvVar(exp[key], ActByteStr())
            else:
                assert False, "unsupported environment variable type"

        elif "entry" in keys:
            # storage item; with timing either pre or post
            assert "timing" in keys, "Missing 'timing' key"
            assert "type" in exp["entry"], "Missing 'type' key"
            assert "item" in exp["entry"], "Missing 'item' key"
            if exp["timing"] == "Pre":
                if exp["entry"]["type"] == "int":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Pre(), ActInt())
                elif exp["entry"]["type"] == "bool":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Pre(), ActBool())
                elif exp["entry"]["type"] == "bytestring":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Pre(), ActByteStr())
                else: 
                    assert False, "unsupported 'type' value" 
            elif exp["timing"] == "Post":
                if exp["entry"]["type"] == "int":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Post(), ActInt())
                elif exp["entry"]["type"] == "bool":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Post(), ActBool())
                elif exp["entry"]["type"] == "bytestring":
                    return StorageItem(parse_storageloc(exp["entry"]["item"]), Post(), ActByteStr())
                else: 
                    assert False, "unsupported 'type' value: " + exp["entry"]["type"] 
            else:
                assert False, "unsupported 'timing' value: " + exp["timing"] 

        elif "expression" in keys: 
            assert isinstance(exp["expression"], Dict), "expression expected to be a dictionary"
            return parse_exp(exp["expression"])
        else:
            assert False, "unknown expression:" + str(exp)


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


def parse_symbol(symbol: str, args: List[Exp])-> Exp:    

        if symbol == "+":
            assert  len(args) == 2, "two arguments expected for +"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Add(args[0],args[1])
        elif symbol == "-":
            assert len(args) == 2, "two arguments expected for -"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Sub(args[0], args[1])
        elif symbol == "*":
            assert len(args) == 2, "two arguments expected for *"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Mul(args[0], args[1])
        elif symbol == "/":
            assert len(args) == 2, "two arguments expected for /"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Div(args[0], args[1])
        elif symbol == "^":
            assert len(args) == 2, "two arguments expected for ^"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Pow(args[0], args[1])
       

        elif symbol == "ite":
            assert len(args) == 3, "three arguments expected for 'ite'"
            assert isinstance(args[0].type, ActBool),"expected boolean condition"
            if all(isinstance(elem.type, ActInt) for elem in args[1:]): 
                return ITE(args[0], args[1], args[2], ActInt())
            elif all(isinstance(elem.type, ActBool) for elem in args):
                return ITE(args[0], args[1], args[2], ActBool())
            elif all(isinstance(elem.type, ActByteStr) for elem in args[1:]):
                return ITE(args[0], args[1], args[2], ActByteStr())
            else:
                assert False, "Unsupported or not matching argument types: " + str(args[1].type) + ", " + str(args[2].type)

        elif symbol == "=/=":
            assert len(args) == 2, "two arguments expected for '=/='"
            all_bool = all(isinstance(elem.type, ActBool) for elem in args)
            all_int = all(isinstance(elem.type, ActInt) for elem in args)
            all_bytestring = all(isinstance(elem.type, ActByteStr) for elem in args)
            assert all_bool or all_int or all_bytestring, "expected arguments to be of same type" 
            return Neq(args[0], args[1])
        elif symbol == "==":
            assert len(args) == 2, "two arguments expected for '=='"
            # all_bool = all(isinstance(elem.type, ActBool) for elem in args)
            # all_int = all(isinstance(elem.type, ActInt) for elem in args)
            # all_bytestring = all(isinstance(elem.type, ActByteStr) for elem in args)
            # assert all_bool or all_int or all_bytestring, "expected arguments to be of same type" 
            return Eq(args[0], args[1])

        elif symbol == "and":
            assert len(args) == 2, "two arguments expected for 'and'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return And(args[0], args[1])
        elif symbol == "or":
            assert len(args) == 2, "two arguments expected for 'or'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Or(args[0], args[1])
        elif symbol == "not":
            assert len(args) == 1, "one argument expected for 'not'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Not(args[0])
        elif symbol == "=>":
            assert len(args) == 2, "two arguments expected for '=>'"
            assert all(isinstance(elem.type, ActBool) for elem in args), "expected boolean expression arguments" 
            return Implies(args[0], args[1])

        elif symbol == "<":
            assert len(args) == 2, "two arguments expected for '<'"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Lt(args[0], args[1])
        elif symbol == ">":
            assert len(args) == 2, "two arguments expected for '>'"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Gt(args[0], args[1])
        elif symbol == "<=":
            assert len(args) == 2, "two arguments expected for '<='"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Le(args[0], args[1])
        elif symbol == ">=":
            assert len(args) == 2, "two arguments expected for '>='"
            assert all(isinstance(elem.type, ActInt) for elem in args), "expected integer expression arguments" 
            return Ge(args[0], args[1])
        else:
            assert False, "Unsupported symbol: " + symbol


def parse_stateupdate(update: Dict) -> Exp:

    assert "location" in update, "Missing 'location' key"    
    assert "value" in update, "Missing 'value' key"  
    assert "svar" in update["location"]  , "Missing 'svar' key"

    update_value= parse_exp(update["value"])

    return Eq(
            StorageItem(
                parse_storageloc(update["location"]), 
                Post(),
                update_value.type
            ), 
            update_value
            )
    

def parse_constructor_case(initstore: Dict) ->  Exp:    
    assert "location" in initstore, "Missing 'location' key"    
    assert "value" in initstore, "Missing 'value' key"  
    assert "contract" in initstore["location"], "Missing 'contract' key"

    init_store_value = parse_exp(initstore["value"])
    print("left:", initstore["location"])
    print("right:", initstore["value"])
    print("parsed right:", init_store_value)
    if "var" in initstore["value"].keys():
        if "abitype" in initstore["value"]["var"].keys():
            abitype = parse_abitype(initstore["value"]["var"]["abitype"]["abitype"])
            if abitype == AbiBoolType():
                init_store_value.type = ActBool()
            else:
                init_store_value.type = ActInt()

    return Eq(
            StorageItem(
                parse_storageloc(initstore["location"]), 
                Post(),
                init_store_value.type
            ), 
            init_store_value
            )



def parse_invariants(inv: Dict) -> List[Exp]:
    assert "kind" in inv, "Missing 'kind' key"    
    assert inv["kind"]=="Invariant", "not of kind invariant"  
    assert "predicate" in inv, "Missing 'predicate' key"

    return [parse_exp(elem) for elem in inv["predicate"] ]


def parse_constraints_json(constraints: List) -> List[Exp]:
    res: List[Exp] = []
    for elem in constraints:
        parse_exp(elem)

    return res