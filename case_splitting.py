from pest import *
from classifier import *

def case_split(tree: Tree, hist: List[str], entire_tree: Tree, players: List[Player]) -> List[str]:
    """
    go through the tree probs bottom up and check whether splitting is required.
    if so, adapt name of branch and add new ones acc. to case split
    if not proceed to next node
    """

    new_hist = hist

    if tree.player == None:
        # leaf case
       return new_hist

    else:
        # change to a while loop and remove the dictionary from the condition
        iteration_list: List[Tuple[str, Tree]] = [(child, child_tree) for child, child_tree in tree.children.items()]
        i = 0

        while i < len(iteration_list):
            child = iteration_list[i][0]
            child_tree: Tree = iteration_list[i][1]
            # call recursion first to proceed bottom up
            new_hist_incl_child = case_split(child_tree, new_hist + [child], entire_tree, players)
            new_hist = new_hist_incl_child[:-1]
            new_child = new_hist_incl_child[-1]
            # KIM: take care of upstream beh.
            # KIM: repeat for preconditions
            # print("next history")
            # print(new_hist_incl_child)
            # if a split is required, "split" is true
            # is dependent returns a possible case_splitting point candidate, which still has to be checked
            split, splitting_point_candidate, case_condition = is_dependent(child_tree.beh_case + child_tree.preconditions,\
                                            child_tree.interface, new_hist_incl_child, entire_tree)
            if split:
                assert isinstance(splitting_point_candidate, List)
                assert isinstance(case_condition, List)
                # we check if the case splitting point is the correct one
                good_split = check_splitting_point(splitting_point_candidate, case_condition, entire_tree, players, new_hist_incl_child)
                splitting_point = splitting_point_candidate
                # if not we walk up the thee to the root to find the correct place of splitting
                while not good_split and len(splitting_point)>0:
                    splitting_point = splitting_point[:-1]
                    good_split = check_splitting_point(splitting_point, case_condition, entire_tree, players, new_hist_incl_child)

                if good_split:
                    # print("splitting point")
                    # print(splitting_point)

                    # compute the condition to be added to the splitting point node (i.e. remove player in range constraints and
                    # formulae equiv to preconditions of the splitting point)
                    split_constraint = compute_split_constraint(splitting_point, case_condition, entire_tree, players)
                    split_constraint = remove_trivial_conditions(split_constraint) 

                    # copy the subtree after splitting_point, the original one tagged condition, the new one tagged not conditon
                    relative_dep_history = hist[len(splitting_point):] + [new_child]
                    child_neg = copy_subtree_without_dep_behav(walk_the_tree(entire_tree, splitting_point), relative_dep_history)
                    child_pos = walk_the_tree(entire_tree, splitting_point)
                    name_addendum = ""
                    assert len(split_constraint) > 0 
                    for exp in split_constraint:
                        name_addendum = name_addendum + "_" + exp.to_string()
                    name_addendum = name_addendum[1:]
                    child_name_neg = splitting_point[-1] + '_NOT(' + name_addendum + ')'
                    child_name_pos = splitting_point[-1] + '_' + name_addendum

                    # add contraints to split_constraints
                    child_neg.split_constraints.append(Not(conjoin(split_constraint)))
                    child_pos.split_constraints.extend(split_constraint)

                    # align the histories and trackers according to new names
                    adapt_tree(splitting_point, child_name_neg, child_neg) # the players don't show up in the histories anywhere, is this an issue? 
                    adapt_tree(splitting_point, child_name_pos, child_pos)

                    # TO DO adapt names of histories in histitems, upstreams etc,
                    # for both branches: childname and splitting_point[-1] (which still has to be changed to splitting_point[-1]+ str(split_constraint))

                    subtree = walk_the_tree(entire_tree, splitting_point[:-1])
                    subtree.children[child_name_pos] = subtree.children.pop(splitting_point[-1])
                    subtree.add_child(child_neg, child_name_neg) # add the child_neg as a sibling of the splitting_point

                    # entire_tree.structure()
                    # print(child_name_pos)
                    new_hist = splitting_point[:-1] + [child_name_pos] + new_hist[len(splitting_point):]
                 
                else: # implement this later
                    print("Warning: need another tree")
                    # for now just in the split conditions of the root
                    entire_tree.split_constraints.extend(case_condition)
            
            
            # rename current child accordingly in iteration_list, s.t. in the future not added
            iteration_list[i] = (new_child, iteration_list[i][1])

            # check which children are new and append these to iteration list
            to_add = []
            for child, child_tree in tree.children.items():
                is_eq = [child == elem[0] for elem in iteration_list]
                if not any(is_eq):
                    # print("new_hist")
                    # print(new_hist)
                    # print("child")
                    # print(child)
                    # print("new_child")
                    # print(new_child)
                    # print("iteration_list")
                    # print([elem[0] for elem in iteration_list])
                    to_add.append((child, child_tree))


            iteration_list.extend(to_add)
            i = i+1

        return new_hist

def conjoin(elements: List[Exp]) -> Exp:
    if len(elements) == 0:
        return Lit(True, ActBool())
    elif len(elements) == 1:
        return elements[0]
    else:
        half: int = int(len(elements)/2) 
        return And(conjoin(elements[:half]), conjoin(elements[half:]))

def compute_split_constraint(hist: List[str], condition: List[Exp], tree: Tree, players: List[Player]) -> List[Exp]:
    """
    remove inrange constraints for players and expressions listed in precondition+split_constraints+beh_case of 
    tree[hist] from condition
    return the shortened list of expressions
    """
    
    split_constraint = []

    player_cons = player_constraints(players)

    for elem in condition:
        equiv_to_prec = [elem.is_equiv(prec) for prec in walk_the_tree(tree, hist).preconditions + 
                                                         walk_the_tree(tree, hist).split_constraints + 
                                                         walk_the_tree(tree, hist).beh_case]
        player_inrange_distinct = [elem.is_equiv(const) for const in player_cons]

        if not any(equiv_to_prec + player_inrange_distinct):
            split_constraint.append(elem)

    return split_constraint


def check_splitting_point(history: List[str], condition: List[Exp], tree: Tree, players: List[Player], dependent_hist: List[str]) -> bool:
    """checks whether a found splitting point in the tree was a good one in the sense that it actual a relevant split,
    i.e. if we are about to split into something different than True and False
    If it was a sensible split return True, ow return False

    history: the splitting point that is being checked
    condition: the preconditions of the dependent behaviour for which we want to find the split for
    tree: the entire tree
    players: all players of the game
    dpendent_history: history to the point in the game for which we need the split
    """

    # first collect all preconditions and updates along history
    previous_constraints = collect_constraints(history, tree)
    # add assumptions that players are distinct and in range
    previous_constraints.extend(player_constraints(players))

    controlled = collect_controlled(dependent_hist[len(history):], walk_the_tree(tree, history), history)

    # translate all into SMT constraints
    smt_previous = [to_smt(elem) for elem in previous_constraints]
    smt_condition = [to_smt(elem) for elem in condition]
    smt_controlled = [to_smt(elem) for elem in controlled]

    split_solver = z3.Solver()
    conjunction = z3.And(*smt_previous)
    negated_cond = z3.Not(z3.And(*smt_condition))
    forall = z3.ForAll(smt_controlled, negated_cond)
    formula = z3.And(conjunction, forall)
    result = split_solver.check(formula)
    

    if result == z3.sat:
        return False

    elif result == z3.unsat:
        return True

    else:
        assert False


def collect_constraints(history: List[str], tree: Tree) -> List[Exp]:
    
    if history == []:
        return []
    
    else: 
        return tree.beh_case + tree.preconditions + tree.split_constraints + tree.updates + collect_constraints(history[1:], tree.children[history[0]])

def collect_controlled(history: List[str], tree: Tree, subtree_hist: List[str]) -> List[Exp]:
     
    if history == []:
        hist_without_players = [elem.split("(")[0] for elem in subtree_hist]
        call_value = HistEnvVar("Callvalue", hist_without_players, ActInt())
        return tree.interface +  [call_value]
    else:
        hist_without_players = [elem.split("(")[0] for elem in subtree_hist]
        call_value = HistEnvVar("Callvalue", hist_without_players, ActInt())
        return tree.interface +  [call_value] + collect_controlled(history[1:], tree.children[history[0]], subtree_hist+[history[0]])

def copy_subtree_without_dep_behav(tree: Tree, dep_behav_hist: List[str]) -> Tree:
    """copies the tree after except the subtree after dep_behav_hist, as this will not be possible in this branch"""

    assert dep_behav_hist != [], "expected a non empty dependent behavior history"

    player = tree.player
    tracker = copy_tracker(tree.tracker)
    beh_case = [exp.copy_exp() for exp in tree.beh_case]
    preconditions = [exp.copy_exp() for exp in tree.preconditions]
    updates = [exp.copy_exp() for exp in tree.updates]
    split_constraints = [exp.copy_exp() for exp in tree.split_constraints]
    smt_constraints = [boo for boo in tree.smt_constraints]
    children: Dict[str, Tree] = dict()
    for key, value in tree.children.items():
        if dep_behav_hist[0] != key:
            children[key] = value.copy()
        else:
            # only copy if not already at the point where we want to remove the branch
            if len(dep_behav_hist) > 1:
                children[key] = copy_subtree_without_dep_behav(value, dep_behav_hist[1:])
    interface: List[Exp] = [var.copy_exp() for var in tree.interface]

    if len(dep_behav_hist) == 1:
        if len(children.keys()) == 1:
            kid = [elem for elem in children.keys()][0]
            action_name_wo_player = kid.split("(")[0]
            assert action_name_wo_player == "ignore"
            # in this case remove the ignore action
            children = dict()
            player = None

    return Tree(player, tracker, beh_case, preconditions, updates, split_constraints, 
                children, smt_constraints, interface)


def remove_trivial_conditions(constraints: List[Exp]) -> List[Exp]:
    
    solver = z3.Solver()
    shortened: List[Exp] = []
    for elem in constraints:
        smt_elem = to_smt(elem)
        is_trivial = solver.check(z3.Not(smt_elem))
        if is_trivial == z3.sat:
            shortened.append(elem)
        else:
            assert is_trivial != z3.unknown

    return shortened


def player_pruning(tree: Tree, hist: List[str], players: List[Player]):

    for childname, child in tree.children.items():
        player_pruning(child, hist+[childname], players)

    to_remove: List[str] = []
    for childname, child in tree.children.items():
        assert isinstance(tree.player, Player)
        to_be_removed = identify_obsolete_branches(childname, child, tree.children, players, tree.player, hist)
        if to_be_removed:
            to_remove.append(childname)

    for elem in to_remove:
        del tree.children[elem]

    return

def identify_obsolete_branches(name: str, branch: Tree, siblings: Dict[str, Tree], players: List[Player], previous_player: Player, hist: List[str]) -> bool:

   
    current_split_constraints = [shorten_history(elem, hist) for elem in branch.split_constraints]
    player_cons = [to_smt(elem) for elem in player_constraints(players)]
    solver = z3.Solver()

    smt_current = [to_smt(elem) for elem in current_split_constraints]

    current = z3.And(*player_cons, *smt_current)


    for siblingname, sibling in siblings.items():
        # don't compare to itself
        if siblingname != name:
            # only the ones with same behavior choice to be compared (same behaviour, equiv constraints, different player)
            if siblingname.split("(")[0] == name.split("(")[0]:

                sibling_constraints = [shorten_history(elem, hist) for elem in sibling.split_constraints]
                smt_sibling = [to_smt(elem) for elem in sibling_constraints]
                other = z3.And(*player_cons, *smt_sibling)
                res = solver.check(z3.Not(current == other))

                assert len(name.split("(")) >= 2, f"{name}"
                assert len(siblingname.split("(")) >= 2, f"{siblingname}"
                pre_current_player = name.split("(")[1]
                pre_sibling_player = siblingname.split("(")[1]
                assert len(pre_current_player.split(")")) >= 1
                assert len(pre_sibling_player.split(")")) >= 1
                current_player = pre_current_player.split(")")[0]
                sibling_player = pre_sibling_player.split(")")[0]
                # if current branch and sibling are equivalent, check which player has precedence according to the
                # players list
                if res == z3.unsat:
                    
                    if len(branch.children) == 0 :
                        # if I am a leaf and the other is not I am obsolete
                        if len(sibling.children) > 0:
                            return True
                        # if I am a leaf and the other is too, it depends on the "players":
                        # if the current player has precendence over the sibling's player it's not necessarily obsolete
                        # otherwise it is
                        assert isinstance(previous_player, Player) 
                        if not current_player_precedence(current_player, sibling_player, previous_player, players):
                            return True   
                    # if I am not a leaf, and the sibling is, I am not necesarily obsolete
                    # if the sibling isn't a leaf either, it again depends on the player precedence
                    elif len(sibling.children) > 0 :
                        assert isinstance(previous_player, Player)                
                        if not current_player_precedence(current_player, sibling_player, previous_player, players):
                            name_wo_player = name.split("(")[0] + str(smt_current)
                            actual_hist = hist + [name_wo_player]
                            print("Possible source of incompleteness of tree structure. The input contains ambiguity with respect to the order of callers:")
                            print(f"At history {actual_hist} it could be player {current_player}'s or player {sibling_player}'s turn.") 
                            return True

    return False

def current_player_precedence(current: str, sibling: str, previous: Player, players: List[Player]) -> bool:

    assert previous in players, "unexpected player"
    previous_index = players.index(previous)
    # new precedence according to previous player
    # is this the logic we want?
    reshaped_players = [elem for elem in players[previous_index+1:]] + [elem for elem in players[:previous_index+1]]

    current_index = find_player_in(current, reshaped_players)
    sibling_index = find_player_in(sibling, reshaped_players)
    assert current_index >= 0, "unexpected player"
    assert sibling_index >= 0, "unexpected player"

    if current_index < sibling_index:
        return True
    elif current_index == sibling_index:
        assert False, "players should be distinct"
    else:
        return False

def find_player_in(name: str, players: List[Player]) -> int:
    for i in range(len(players)):
        if players[i].name == name:
            return i
    return -1


def shorten_history(exp: Exp, history: List[str]) -> Exp:
    
    res: Exp

    # shorten history elements
    if isinstance(exp, HistItem):
        if len(exp.hist) == len(history) + 1:
            res = HistItem(shorten_storage_loc(exp.loc, history), [elem for elem in exp.hist[:-1]], exp.type)
    elif isinstance(exp, HistVar):
        if len(exp.hist) == len(history) + 1:
            res = HistVar(exp.name, [elem for elem in exp.hist[:-1]], exp.type)
    elif isinstance(exp, HistEnvVar):
         if len(exp.hist) == len(history) + 1:
            res = HistEnvVar(exp.name, [elem for elem in exp.hist[:-1]], exp.type)

    # call the function recursively for recursive exp
    elif isinstance(exp, And):
        res = And(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Or):
        res = Or(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Not):
        res = Not(shorten_history(exp.value, history),exp.type)
    elif isinstance(exp, Eq):
        res = Eq(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Neq):
        res = Neq(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Add):
        res = Add(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Sub):
        res = Sub(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Mul):
        res = Mul(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Div):
        res = Div(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Pow):
        res = Pow(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Lt):
        res = Lt(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Le):
        res = Le(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Gt):
        res = Gt(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)
    elif isinstance(exp, Ge):
        res = Ge(shorten_history(exp.left, history), shorten_history(exp.right, history), exp.type)

    # do nothing for the rest + assert some types not present
    elif isinstance(exp, Player):
        res = exp
    else:
        # assert not isinstance(exp, Implies)
        # assert not isinstance(exp, ITE)
        # assert not isinstance(exp, InRange)
        # assert not isinstance(exp, Var)
        # assert not isinstance(exp, EnvVar)
        # assert not isinstance(exp, StorageItem)
        # equivalent too:
        assert isinstance(exp, Lit)
        res = exp.copy_exp()

    return res


def shorten_storage_loc(loc: StorageLoc, history: List[str]) -> StorageLoc:

    if isinstance(loc, VarLoc):
        return loc.copy_loc()
    elif isinstance(loc, ContractLoc):
        return ContractLoc(shorten_storage_loc(loc.loc, history), loc.contract, loc.field)
    else: 
        assert isinstance(loc,MappingLoc)
        return MappingLoc(shorten_storage_loc(loc.loc, history), [shorten_history(elem, history) for elem in loc.args])
