from pest import *


def is_dependent(constraints: List[Exp], tracker: Tracker, interface: List[Exp],
                 hist: List[str]) \
                                                     -> Tuple[bool, List[Upstream]]:
    
    tr_constraints: List[SymVar] = []
    for_all_vars: List[SymVar] = []
    for elem in constraints:
        cons, vars = apply_tracker(elem, tracker)
        smt_cons = to_smt(cons)
        tr_constraints.append(smt_cons)
        smt_vars = [to_smt(var) for var in vars]
        for_all_vars.extend(smt_vars)

    smt_interface: List[SymVar] = []
    for elem in interface:
        smt_interface.append(to_smt(elem))
    call_value = HistEnvVar("Callvalue", hist, ActInt())
    smt_call_value = to_smt(call_value)
    conjunct = z3.And(*tr_constraints)
    for_all = z3.ForAll(for_all_vars, conjunct)
    exists = z3.Exists(interface + [smt_call_value], for_all)

    solver = z3.Solver()
    dependent = solver.check(exists)
    print(exists)

    if dependent == z3.sat:
        print("sat")
        return False, []
    
    elif dependent == z3.unsat:
        print("unsat, requires split")
        return True, []

    else:
        assert dependent == z3.unknown
        assert False, "Warning: Z3 returned unknown"


def apply_tracker(exp: Exp, tracker: Tracker) -> Tuple[Exp, List[Exp]]:
    
    # all except storage vars remain the same

    if isinstance(exp, HistItem):
        for tracker_elem in tracker:
            if exp.is_equiv(tracker_elem.item):
                return tracker_elem.value, extract_vars(tracker_elem.value)

        assert False, "history item was not found in the tracker"

    elif isinstance(exp, And):
        left, l_var = apply_tracker(exp.left, tracker)
        right, r_var = apply_tracker(exp.right, tracker)
        return And(left, right), l_var + r_var 
    
    # continue here
    return exp, []

def extract_vars(value: Exp) -> List[Exp]:
    pass