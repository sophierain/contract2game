from .ast import *
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

    for key, value in store["storages"].items():
        store_dict[key] = dict()
        if isinstance(store["storages"][key], Dict):
            for nested_key, nested_value in value.items():
                store_dict[key][nested_key] = parse_slottype(nested_value)

    return store_dict


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
        return MappingType([parse_valuetype(elem) for elem in slottype["ixTypes"]], parse_valuetype(slottype["resType"]))

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
    assert "behaviours" in contract, "Missing 'behaviours' key"
    assert "contract" in contract["constructor"], "Missing 'contract' key at 'contract['constructor']'"

    return Contract(contract["constructor"]["contract"], parse_constructor(contract["constructor"]), [parse_behavior(elem) for elem in contract["behaviours"]])


def parse_constructor(ctor: Dict)-> Constructor:

    assert ctor["kind"]=="Constructor", "'kind' key does not match 'Constructor'"
    assert "initialStorage" in ctor, "Missing 'initialStorage' key"
    assert "interface" in ctor, "Missing 'interface' key"
    assert "invariants" in ctor, "Missing 'invariants' key"
    assert "preConditions" in ctor, "Missing 'preConditions' key"
    assert "postConditions" in ctor, "Missing 'postConditions' key"

    return Constructor(
                        parse_interface(ctor["interface"]),
                        [parse_initstore(elem) for elem in ctor["initialStorage"] ],
                        [parse_boolexp(elem) for elem in ctor["preConditions"] ],
                        [parse_boolexp(elem) for elem in ctor["postConditions"] ],
                        [exp  for elem in ctor["invariants"] for exp in parse_invariants(elem)]
                        )


def parse_behavior(behv: Dict) -> Behavior:
    assert behv["kind"]=="Behaviour", "'kind' key does not match 'Behaviour'"
    assert "name" in behv, "Missing 'name' key"
    assert "interface" in behv, "Missing 'interface' key"
    assert "case" in behv, "Missing 'case' key"
    assert "preConditions" in behv, "Missing 'preConditions' key"
    assert "postConditions" in behv, "Missing 'postConditions' key"
    assert "returns" in behv, "Missing 'returns' key"
    assert "stateUpdates" in behv, "Missing 'stateUpdates' key"

    update = []

    for elem in behv["stateUpdates"]:
        if "rewrite" in elem:
            update.append(parse_stateupdate(elem["rewrite"]))
        elif "location" in elem:
            update.append(parse_stateupdate(elem))
        else:
            assert "constant" in elem

    return Behavior(
                    behv["name"],
                    parse_interface(behv["interface"]),
                    [parse_boolexp(elem) for elem in behv["case"] ],
                    [parse_boolexp(elem) for elem in behv["preConditions"] ],
                    [parse_boolexp(elem) for elem in behv["postConditions"] ],
                    parse_exp(behv["returns"]),
                    update
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


def parse_boolexp(boolexp: Dict) -> Exp:
    res = parse_exp(boolexp)
    assert res.type == ActBool(), "not a boolean expression"
    return res


def parse_intexp(intexp: Dict) -> Exp:
    res = parse_exp(intexp)
    assert res.type == ActInt(), "not an integer expression"
    return res


def parse_exp(exp: Dict) -> Exp:
    keys = exp.keys()
    if "symbol" in keys:
        #recursive case
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
            return parse_symbol(exp["symbol"], [parse_exp(elem) for elem in exp["args"]])

    else:
        # Base Case
        if "literal" in keys:
            # Literal; either int, bool or bytestring
            assert "type" in keys, "Missing 'type' key"
            if exp["type"] == "int":
                return Lit(int(exp["literal"]), ActInt())
            elif exp["type"] == "bool":
                return Lit(bool(exp["literal"]), ActBool())
            elif exp["type"] == "bytestring":
                return Lit(str(exp["literal"]), ActByteStr())
            else:
                assert False, "unsupported literal type"

        elif "var" in keys:
            # Variable; either int or bool
            assert "type" in keys, "Missing 'type' key"
            if exp["type"] == "int":
                return Var(exp["var"], ActInt())
            elif exp["type"] == "bool":
                return Var(exp["var"], ActBool())
            elif exp["type"] == "bytestring":
                return Var(exp["var"], ActByteStr())
            else:
                assert False, "unsupported variable type"

        elif "envValue" in keys:
            # environment value; int, bool or bytestring
            assert "type" in keys, "Missing 'type' key"
            if exp["type"] == "int":
                return EnvVar(exp["envValue"], ActInt())
            elif exp["type"] == "bool":
                return EnvVar(exp["envValue"], ActBool())
            elif exp["type"] == "bytestring":
                return EnvVar(exp["envValue"], ActByteStr())
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
            all_bool = all(isinstance(elem.type, ActBool) for elem in args)
            all_int = all(isinstance(elem.type, ActInt) for elem in args)
            all_bytestring = all(isinstance(elem.type, ActByteStr) for elem in args)
            assert all_bool or all_int or all_bytestring, "expected arguments to be of same type"
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
    assert "type" in update["location"]  , "Missing 'type' key"
    assert "item" in update["location"]  , "Missing 'item' key"

    if update["location"]["type"]== "int":
        return Eq(
                StorageItem(
                    parse_storageloc(update["location"]["item"]),
                    Post(),
                    ActInt()
                ),
                parse_exp(update["value"])
                )
    elif update["location"]["type"]== "bool":
        return Eq(
                StorageItem(
                    parse_storageloc(update["location"]["item"]),
                    Post(),
                    ActBool()
                ),
                parse_exp(update["value"])
                )
    elif update["location"]["type"]== "bytestring":
        return Eq(
                StorageItem(
                    parse_storageloc(update["location"]["item"]),
                    Post(),
                    ActByteStr()
                ),
                parse_exp(update["value"])
                )
    else:
        assert False, "unsupported StorageItem type: " + update["location"]["type"]


def parse_initstore(initstore: Dict) ->  Exp:
    assert "location" in initstore, "Missing 'location' key"
    assert "value" in initstore, "Missing 'value' key"
    assert "type" in initstore["location"]  , "Missing 'type' key"
    assert "item" in initstore["location"], "Missing 'item' key"

    if initstore["location"]["type"]== "int":
        return Eq(
                StorageItem(
                    parse_storageloc(initstore["location"]["item"]),
                    Pre(),
                    ActInt()
                ),
                parse_exp(initstore["value"])
                )
    elif initstore["location"]["type"]== "bool":
        return Eq(
                StorageItem(
                    parse_storageloc(initstore["location"]["item"]),
                    Pre(),
                    ActBool()
                ),
                parse_exp(initstore["value"])
                )
    elif initstore["location"]["type"]== "bytestring":
        return Eq(
                StorageItem(
                    parse_storageloc(initstore["location"]["item"]),
                    Pre(),
                    ActByteStr()
                ),
                parse_exp(initstore["value"])
                )
    else:
        assert False, "unsupported StorageItem type: " + str(initstore["location"]["type"])


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
