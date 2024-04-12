from pest import *
import itertools

def is_dependent(constraints: List[Exp], tracker: Tracker, interface: List[Exp],
                 hist: List[str], tree: Tree) \
                                                     -> Tuple[bool, List[Upstream]]:

    tr_cons: List[Exp] = []
    forall_vars: List[Exp] = []
    forall_player_vars: List[Exp] = []
    for elem in constraints:
        # cons are the constraints where tracker and players have been applied,
        # vars is the list of all forall quantified variables, listing the caller not the player
        # player_vars is the list of all forall quantified variables, where the callers have been replaced by the players
        cons, vars, player_vars = apply_tracker(elem, tree, hist)
        tr_cons.append(cons)
        forall_vars.extend(vars)
        forall_player_vars.extend(player_vars)
 

    # remove doubles from forall_vars
    remove_doubles(forall_vars)
    remove_doubles(forall_player_vars)

    # remove exists_vars from forall_vars
    hist_without_players = [elem.split("(")[0] for elem in hist]
    call_value = HistEnvVar("Callvalue", hist_without_players, ActInt())
    exists_vars = interface + [call_value]
    remove_list(forall_vars, exists_vars)
    remove_list(forall_player_vars, exists_vars)

  
    # check the forall vars for preconditions of previous fcts, use the callers!
    # prev_prec using players instead of callers
    _, additional_player_foralls, prev_prec = compute_prev_prec(tree, forall_vars, forall_player_vars ,hist) 


    final_forall = additional_player_foralls + forall_player_vars
    remove_doubles(final_forall)
    assert len(final_forall) == len(additional_player_foralls + forall_player_vars)

    quant_players = []
    for var in final_forall:
        if isinstance(var, Player):
            quant_players.append(var)
    # add inrange preconditions for all quantified players
    for player in quant_players:
        prev_prec.append(Le(Lit(0, ActInt()), player))
        prev_prec.append(Le(player, Lit((2**256) -1, ActInt())))
    # add distinctness preconditions for all pairs of players
    player_pairs = itertools.combinations(quant_players, 2)
    for pair in player_pairs:
        prev_prec.append(Neq(pair[0], pair[1]))


    # only proceed if there are problematic variables, otherwise trivially no case split required
    if len(final_forall)>0:
        # translate to smt
        smt_forall = [to_smt(var) for var in final_forall]
        smt_exists = [to_smt(var) for var in exists_vars]

        smt_cons = [to_smt(cons) for cons in tr_cons]
        smt_prec = [to_smt(prec) for prec in prev_prec]

        conjunct = z3.And(*smt_cons)
        precondition = z3.And(*smt_prec)
        exists = z3.Exists(smt_exists, conjunct)
        implication = z3.Implies(precondition, exists)
        for_all = z3.ForAll(smt_forall, implication)
        

        solver = z3.Solver()

        print("formula")
        print(final_forall)
        print(prev_prec)
        print("->")
        print(exists_vars)
        print(tr_cons)
        print()

        print("SMT formula")
        print(for_all)
        print()

        dependent = solver.check(for_all)
        print("post SMT")

        if dependent == z3.sat:
            print("sat, no split")
            return False, []
        
        elif dependent == z3.unsat:
            print("unsat, requires split")
            return True, []

        else:
            assert dependent == z3.unknown
            assert False, "Warning: Z3 returned unknown"
        
    else:
        print("sat, no split")
        return False, []


def remove_doubles(exps: List[Exp]):
    """
    removes double entries from the list
    """
    to_remove: List[int] = []

    for i in range(len(exps)):
        assert isinstance(exps[i], HistEnvVar) or \
                isinstance(exps[i], HistVar) or isinstance(exps[i], Player), "unexpected expression type"
        
        for j in range(len(exps)- i - 1):
            ind = i + j + 1
            if exps[i].is_equiv(exps[ind]):
                to_remove = [i] + to_remove
                break

    # remove double values
    for k in to_remove:
        x = exps.pop(k)

    return


def remove_list(exps: List[Exp], remv: List[Exp]):
    """
    removes entries of revm from exps, if they occurred there
    """
    to_remove: List[int] = []

    for i in range(len(remv)):
        assert isinstance(remv[i], HistEnvVar) or \
                isinstance(remv[i], HistVar) or isinstance(remv[i], Player), "unexpected expression type"
        
        for j in range(len(exps)):
            if remv[i].is_equiv(exps[j]):
                assert j not in to_remove
                to_remove = [j] + to_remove
                break

    # remove double values
    to_remove.sort(reverse = True)
    for k in to_remove:
        x = exps.pop(k)

    return


def apply_tracker(exp: Exp, tree: Tree, history: List[str]) -> Tuple[Exp, List[Exp], List[Exp]]:
    """
    returns the new expression where the storage item is replaced by its current value 
    (+iteration in upstream) as the first argument
    and the list of variables that occur in those value terms
    """
    # all except storage vars remain the same
    if isinstance(exp, HistItem):
        tracker = walk_the_tree(tree, history[:len(exp.hist)]).tracker

        for tracker_elem in tracker:
             if exp.is_equiv(tracker_elem.item):
                return apply_tracker(tracker_elem.value, tree, history)

        assert False, "history item was not found in the tracker"

    elif isinstance(exp, Lit):
        return exp, [], []
    
    elif isinstance(exp, HistVar):
        return exp, [exp], [exp]
    
    elif isinstance(exp, HistEnvVar):
        if exp.name == "Caller":
            # find caller in the tracker
            tracker = walk_the_tree(tree, history).tracker
            for tracker_elem in tracker:
                if exp.is_equiv(tracker_elem.item):
                    assert isinstance(tracker_elem.value, Player)
                    return tracker_elem.value, [exp], [tracker_elem.value]
            print([elem.item for elem in tracker])
            assert False, "caller was not found in the tracker"
            
        return exp, [exp], [exp]
    
    elif isinstance(exp, Player):
        assert False, "player not expected in precondition"

    elif isinstance(exp, And):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return And(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Or):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Or(left, right), l_var + r_var, lp_var + rp_var

    elif isinstance(exp, Not):
        value, var, p_var = apply_tracker(exp.value, tree, history)
        return Not(value), var, p_var
    
    elif isinstance(exp, ITE):
        condition, c_var, cp_var = apply_tracker(exp.condition, tree, history)
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return ITE(condition, left, right, exp.type), l_var + r_var + c_var, lp_var + rp_var + cp_var

    elif isinstance(exp, Eq):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Eq(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Neq):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Neq(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Add):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Add(left, right), l_var + r_var, lp_var + rp_var

    elif isinstance(exp, Sub):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Sub(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Mul):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Mul(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Div):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Div(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Pow):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Pow(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Lt):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Lt(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Le):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Le(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Gt):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Gt(left, right), l_var + r_var, lp_var + rp_var
    
    elif isinstance(exp, Ge):
        left, l_var, lp_var = apply_tracker(exp.left, tree, history)
        right, r_var, rp_var = apply_tracker(exp.right, tree, history)
        return Ge(left, right), l_var + r_var, lp_var + rp_var

    else: 
        # shouldn't see any implies nor inrange at this point (CNF)
        assert False, "unexpected Exp type"


def walk_the_tree(tree: Tree, hist: List[str]) -> Tree:
    
    if hist == []:
        return tree
    
    else:
        assert hist[0] in tree.children.keys(), "history behavior not found in tree"
        return walk_the_tree(tree.children[hist[0]] ,hist[1:])
    

def compute_prev_prec(tree: Tree, forall_vars: List[Exp], forall_player_vars: List[Exp], starting_point_history: List[str]) -> Tuple[List[Exp], List[Exp], List[Exp]]:
    """
    takes the entire player enhanced state tree (pest), and the list of computed forall variables (with callers).
    Computes (already satisfied) preconditions of previous behaviors and all the other variables that occur 
    in these as additional for all variables
    """

    additional_prec = []
    additional_foralls = []
    additional_player_foralls =[]

    for forall_var in forall_vars:
        assert isinstance(forall_var, HistVar) or isinstance(forall_var, HistEnvVar)
        var_hist = forall_var.hist
        # find preconditions at that hist, where the forall_var occurs
        if len(starting_point_history) == len(var_hist):
            continue
        subtree = walk_the_tree(tree, starting_point_history[:len(var_hist)])
        prev_prec = subtree.beh_case + subtree.preconditions
        for prec in prev_prec:
            # does forall_var occur here?
            new_prec, new_var, new_p_var = apply_tracker(prec, tree, starting_point_history[:len(var_hist)])
            # if it does occur we keep the precondition and the additional forall values
            if forall_var in new_var:
                additional_prec.append(new_prec)
                additional_foralls.extend(new_var)
                additional_player_foralls.extend(new_p_var)

    # remove doubles
    remove_doubles(additional_foralls)
    remove_doubles(additional_player_foralls)
    # remove the existing forall_vars
    for elem in forall_vars:
        if elem in additional_foralls:
            additional_foralls.remove(elem)
    for elem in forall_player_vars:
        if elem in additional_player_foralls:
            additional_player_foralls.remove(elem)

    rec_forall = []
    rec_prec = []
    rec_p_forall = []
    if len(additional_foralls) > 0:
        rec_forall, rec_p_forall, rec_prec = compute_prev_prec(tree, additional_foralls, additional_player_foralls, starting_point_history)

    return additional_foralls + rec_forall, additional_player_foralls + rec_p_forall, additional_prec + rec_prec

