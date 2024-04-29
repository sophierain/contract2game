from pest import *
from classifier import *

def case_split(tree: Tree, hist: List[str], entire_tree: Tree, players: List[Player]):
    """
    go through the tree probs bottom up and check whether splitting is required.
    if so, adapt name of branch and add new ones acc. to case split
    if not proceed to next node
    """

    if tree.player == None:
        # leaf case
       return

    else:
        for child, child_tree in tree.children.items():
            # call recursion first to proceed bottom up
            case_split(child_tree, hist + [child], entire_tree, players)

            # KIM: take care of upstream beh.
            # KIM: repeat for preconditions
            print(hist+[child])
            # if a split is required, "split" is true
            # is dependent returns a possible case_splitting point candidate, which still has to be checked
            split, splitting_point_candidate, case_condition = is_dependent(child_tree.beh_case + child_tree.preconditions,\
                                            child_tree.interface, hist+[child], entire_tree)
            if split:
                # we check if the case splitting point is the correct one
                good_split = check_splitting_point(splitting_point_candidate, case_condition, entire_tree, players, hist+[child])
                splitting_point = splitting_point_candidate
                # if not we walk up the thee to the root to find the correct place of splitting
                while not good_split and len(splitting_point)>0:
                    splitting_point = splitting_point[:-1]
                    good_split = check_splitting_point(splitting_point, case_condition, entire_tree, players, hist+[child])

                if good_split:
                 print("splitting point")
                 print(splitting_point)
                else:
                    assert False, "need another tree"

                # compute the condition to be added to the splitting point node (i.e. remove player in range constraints and
                # formulae equiv to preconditions of the splitting point)
                split_constraint = compute_split_constraint(splitting_point, case_condition, entire_tree)
                # copy the subtree after splitting_point, the original one tagged condition, the new one tagged not conditon
                # for original one add condition to split_conditions, for new one add not condition and remove the dependent behavior
                

        return


def compute_split_constraint(hist: List[str], condition: List[Exp], tree: Tree) -> List[Exp]:
    pass

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
    player_pairs = itertools.combinations(players, 2)
    for pair in player_pairs:
        previous_constraints.append(Neq(pair[0], pair[1]))
    for player in players:
        previous_constraints.append(Le(Lit(0, ActInt()), player))
        previous_constraints.append(Le(player, Lit((2**160) -1, ActInt())))

    controlled = collect_controlled(dependent_hist[len(history):], walk_the_tree(tree, history), history)
    # print("previous constraints")
    # print(previous_constraints)
    # print("controlled Vars")
    # print(controlled)
    # print("current constriants")
    # print(condition)


    # translate all into SMT constraints
    smt_previous = [to_smt(elem) for elem in previous_constraints]
    smt_condition = [to_smt(elem) for elem in condition]
    smt_controlled = [to_smt(elem) for elem in controlled]

    split_solver = z3.Solver()
    conjunction = z3.And(*smt_previous)
    negated_cond = z3.Not(z3.And(*smt_condition))
    forall = z3.ForAll(smt_controlled, negated_cond)
    formula = z3.And(conjunction, forall)
    # print(formula)
    result = split_solver.check(formula)
    

    if result == z3.sat:
        # model = split_solver.model()
        # print("model")
        # print(model)
        # print("need a splitting point further up")
        return False

    elif result == z3.unsat:
        # print("good splitting point")
        return True

    else:
        assert False


def collect_constraints(history: List[str], tree: Tree) -> List[Exp]:
    
    if history == []:
        return []
    
    else: 
        return tree.beh_case + tree.preconditions + tree.updates + collect_constraints(history[1:], tree.children[history[0]])

def collect_controlled(history: List[str], tree: Tree, subtree_hist: List[str]) -> List[Exp]:
     
    if history == []:
        hist_without_players = [elem.split("(")[0] for elem in subtree_hist]
        call_value = HistEnvVar("Callvalue", hist_without_players, ActInt())
        return tree.interface +  [call_value]
    else:
        hist_without_players = [elem.split("(")[0] for elem in subtree_hist]
        call_value = HistEnvVar("Callvalue", hist_without_players, ActInt())
        return tree.interface +  [call_value] + collect_controlled(history[1:], tree.children[history[0]], subtree_hist+[history[0]])



