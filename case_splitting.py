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
        for child, child_tree in tree.children.items():
            # call recursion first to proceed bottom up
            new_hist_incl_child = case_split(child_tree, new_hist + [child], entire_tree, players)
            new_hist = new_hist_incl_child[:-1]
            new_child = new_hist_incl_child[-1]
            # KIM: take care of upstream beh.
            # KIM: repeat for preconditions
            print(new_hist_incl_child)
            # if a split is required, "split" is true
            # is dependent returns a possible case_splitting point candidate, which still has to be checked
            split, splitting_point_candidate, case_condition = is_dependent(child_tree.beh_case + child_tree.preconditions,\
                                            child_tree.interface, new_hist_incl_child, entire_tree)
            if split:
                # we check if the case splitting point is the correct one
                good_split = check_splitting_point(splitting_point_candidate, case_condition, entire_tree, players, new_hist_incl_child)
                splitting_point = splitting_point_candidate
                # if not we walk up the thee to the root to find the correct place of splitting
                while not good_split and len(splitting_point)>0:
                    splitting_point = splitting_point[:-1]
                    good_split = check_splitting_point(splitting_point, case_condition, entire_tree, players, new_hist_incl_child)

                if good_split:
                    print("splitting point")
                    print(splitting_point)

                    # compute the condition to be added to the splitting point node (i.e. remove player in range constraints and
                    # formulae equiv to preconditions of the splitting point)
                    split_constraint = compute_split_constraint(splitting_point, case_condition, entire_tree, players)
                    

                    # copy the subtree after splitting_point, the original one tagged condition, the new one tagged not conditon
                    relative_dep_history = hist[len(splitting_point):] + [new_child]
                    child_neg = copy_subtree_without_dep_behav(walk_the_tree(entire_tree, splitting_point), relative_dep_history)
                    child_pos = walk_the_tree(entire_tree, splitting_point)
                    child_name_neg = splitting_point[-1] + "_NOT(" + str(split_constraint) + ")"
                    child_name_pos = splitting_point[-1] + "_" + str(split_constraint)

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
                    new_hist = splitting_point[:-1] + [child_name_pos] + new_hist[len(splitting_point):]
                 
                else: # implement this later
                    print("Warning: need another tree")
                    # for now just in the split conditions of the root
                    entire_tree.split_constraints.extend(case_condition)

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

def caller_dep(constr: Exp, tracker: Tracker) -> bool:
    pass

def caller_split(tree: Tree, child: Tree, constr: Exp):
    pass

def hist_split(tree: Tree, child: Tree, constr: Exp):
    pass

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

def adapt_tree(hist: List[str], name: str, tree: Tree):
    """ 
    aligns the history expressions and tracker elements according to the new name 'name'. 
    The last entry of hist is the old name of the branch leading to tree.
    e.g. hist: ["a", "b"], name "b_new", tree is the subtree after choices "a", then "b"

    modifies the tree such that it contains the correct new name of the choice
    """
    # player names not listed in histitems, hence restruct hist accordingly
    no_player_hist = []
    for elem in hist:
        assert len(elem.split("("))>= 2, elem
        assert len(elem.split(")"))>= 2, elem
        first_part = elem.split("(")[0]
        second_part = elem[len(elem.split(")")[0])+1:]
        no_player_hist.append(first_part + second_part)

    assert len(name.split("("))>= 2, name
    assert len(name.split(")"))>= 2, name
    first_part = name.split("(")[0]
    second_part = name[len(name.split(")")[0])+1:]
    no_player_name =(first_part + second_part)

    tree.tracker = adapt_tracker(no_player_hist, no_player_name, tree.tracker)
    tree.beh_case = [adapt_hist(no_player_hist, no_player_name, exp) for exp in tree.beh_case]
    tree.preconditions = [adapt_hist(no_player_hist, no_player_name, exp) for exp in tree.preconditions]
    tree.updates = [adapt_hist(no_player_hist, no_player_name, exp) for exp in tree.updates]
    tree.split_constraints = [adapt_hist(no_player_hist, no_player_name, exp) for exp in tree.split_constraints]
    for child in tree.children.keys():
        adapt_tree(hist, name, tree.children[child])
    # smt_constraints no longer used
    tree.smt_constraints = [] 
    tree.interface = [adapt_hist(no_player_hist, no_player_name, exp) for exp in tree.interface]
    return 

def adapt_hist(hist: List[str], name: str, exp: Exp) -> Exp:
    """
    changes the old name hist[-1] to the new_name name in exp, if it is a hist item younger or equal to hist 
    """

    if isinstance(exp, HistItem):
        # take care of loc for mappings
        if isinstance(exp.loc, MappingLoc):
            loc = MappingLoc(exp.loc.loc.copy_loc(), [adapt_hist(hist, name, elem) for elem in exp.loc.args])
        else:
            loc = exp.loc.copy_loc()


        if len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist[:-1] + [name] + exp.hist[len(hist):]

        return HistItem(loc, new_hist, exp.type)

    elif isinstance(exp, Lit):
        return exp.copy_exp()
    
    elif isinstance(exp, HistVar):

        if len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist[:-1] + [name] + exp.hist[len(hist):]
        return HistVar(exp.name, new_hist, exp.type)
    
    elif isinstance(exp, HistEnvVar):

        if len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist[:-1] + [name] + exp.hist[len(hist):]
        return HistEnvVar(exp.name, new_hist, exp.type)
    
    elif isinstance(exp, Player):
        return exp

    elif isinstance(exp, And):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return And(left, right)
    
    elif isinstance(exp, Or):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Or(left, right) 

    elif isinstance(exp, Not):
        value = adapt_hist(hist, name, exp.value)
        return Not(value)
    
    elif isinstance(exp, ITE):
        condition = adapt_hist(hist, name, exp.condition)
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return ITE(condition, left, right, exp.type)

    elif isinstance(exp, Eq):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Eq(left, right) 
    
    elif isinstance(exp, Neq):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Neq(left, right) 
    
    elif isinstance(exp, Add):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Add(left, right) 

    elif isinstance(exp, Sub):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Sub(left, right) 
    
    elif isinstance(exp, Mul):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Mul(left, right) 
    
    elif isinstance(exp, Div):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Div(left, right) 
    
    elif isinstance(exp, Pow):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Pow(left, right) 
    
    elif isinstance(exp, Lt):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Lt(left, right) 
    
    elif isinstance(exp, Le):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Le(left, right) 
    
    elif isinstance(exp, Gt):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Gt(left, right) 
    
    elif isinstance(exp, Ge):
        left = adapt_hist(hist, name, exp.left)
        right = adapt_hist(hist, name, exp.right)
        return Ge(left, right) 

    else: 
        # shouldn't see any implies nor inrange at this point (CNF)
        assert False, "unexpected Exp type"

def adapt_tracker(tracker_hist: List[str], name: str, tracker: Tracker) -> Tracker:
    """
    if upstream younger or equal to hist, change name of hist[-1] to name
    fresh instances of item and upstream as those can change in a tracker;
    value is shallowly assigned 
    """

    # tracker_hist = []
    # for elem in hist:
    #     assert len(elem.split("(")) == 2 
    #     assert len(elem.split(")")) == 2 
    #     tracker_hist.append(elem.split("(")[0] + elem.split(")")[1])

    new_tracker: Tracker = []

    for elem in tracker:
        new_item = adapt_hist(tracker_hist, name, elem.item)
        if len(elem.upstream) < len(tracker_hist):
            assert all([tracker_hist[i] == elem.upstream[i] for i in range(len(elem.upstream))] )
            new_upstream = elem.upstream
        else:
            assert all([tracker_hist[i] == elem.upstream[i] for i in range(len(tracker_hist))] )
            new_upstream = tracker_hist[:-1] + [name] + elem.upstream[len(tracker_hist):]
        new_value = adapt_hist(tracker_hist, name, elem.value)
        new_tracker.append(TrackerElem(new_item, new_value, new_upstream))

    return new_tracker