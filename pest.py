from act_ast import Exp
from state_tree import *




def contract2pest(contract: Contract, extra_constraints: List[Exp], \
                  store: Storage, players: List[Player]) -> Tree:

    state_tree = contract2tree(contract, extra_constraints, store)
    assert len(players) > 1, "at least 2 players required"

    print("state_tree successfully generated")
    # state_tree.structure()

    generate_pest([], state_tree, players, [], [])

    print("player-enhanced state tree with ignore successfully generated")
    # state_tree.structure()

    prune_pest(state_tree)
    print("pest successfully pruned")
    # state_tree.structure()


    return state_tree


def add_ignore(tree: Tree, hist: List[str]):
    """ add ignore branch
   

    add ignore branch and children are the same as siblings
    """
    # print("add ignore")
    #build a new tree
    # add the not the same player twice constraint and add it as new subtree
    children: Dict[str, Tree] = dict()
    for key, value in tree.children.items():
        children[key] = align_children(value, hist)
        ignore_caller = HistEnvVar("Caller", hist + ["ignore"], ActInt())
        # print(ignore_caller)
        child_caller = HistEnvVar("Caller", hist + ["ignore", key], ActInt())
        # print(child_caller)
        ignore_constr = Neq(ignore_caller, child_caller)
        children[key].preconditions.append(ignore_constr)

    # print("hist that copy update tracker is called with")
    # print(hist)
    tracker = align_tracker(tree.tracker, "ignore", hist)

    beh_case = []
    preconditions = []
    updates = []
    split_constraints = []
    smt_constraints = []

    # beh_case = [align_hist(exp, hist) for exp in tree.beh_case]
    # preconditions = [align_hist(exp, hist) for exp in tree.preconditions]
    # updates = [align_hist(exp, hist) for exp in tree.updates]
    # split_constraints = [align_hist(exp, hist) for exp in tree.split_constraints]
    # probably also off by 1
    # smt_constraints = [boo for boo in tree.smt_constraints]


    assert "ignore" not in tree.children.keys()
    tree.children["ignore"]= Tree(None, tracker, beh_case, preconditions, updates, 
                                  split_constraints, children, smt_constraints, [])
    
    return


def align_children(tree: Tree, hist: List[str]) -> Tree:

    tracker = align_tracker(tree.tracker, "ignore", hist) # adapt copyUpdateTracker
    beh_case = [align_hist(exp, hist) for exp in tree.beh_case]
    preconditions = [align_hist(exp, hist) for exp in tree.preconditions]
    updates = [align_hist(exp, hist) for exp in tree.updates]
    split_constraints = [align_hist(exp, hist) for exp in tree.split_constraints]
    # probably also off by 1, not to be adapted?
    smt_constraints = [boo for boo in tree.smt_constraints]
    interface = [align_hist(exp, hist) for exp in tree.interface]

    children: Dict[str, Tree] = dict()
    for key, value in tree.children.items():
        children[key] = align_children(value, hist)

    return Tree(None, tracker, beh_case, preconditions, updates, 
                                  split_constraints, children, smt_constraints, interface)


def align_hist(exp: Exp, hist: List[str]) -> Exp:
    """ 
    if exp.hist shorter (subhist) than hist, do nothing
    elif they are the same --> add ignore
    elif exp.hist is super hist of hist, then do hist + ignore + rest of exp.hist 
    """

    if isinstance(exp, HistItem):
        # take care of loc for mappings
        if isinstance(exp.loc, MappingLoc):
            loc = MappingLoc(exp.loc.loc.copy_loc(), [align_hist(elem, hist) for elem in exp.loc.args])
        else:
            loc = exp.loc.copy_loc()

        if len(hist) == len(exp.hist):
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"]
        elif len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"] + exp.hist[len(hist):]

        return HistItem(loc, new_hist, exp.type)

    elif isinstance(exp, Lit):
        return exp.copy_exp()
    
    elif isinstance(exp, HistVar):

        if len(hist) == len(exp.hist):
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"]
        elif len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"] + exp.hist[len(hist):]
        return HistVar(exp.name, new_hist, exp.type)
    
    elif isinstance(exp, HistEnvVar):

        if len(hist) == len(exp.hist):
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"]
        elif len(hist) > len(exp.hist):
            for i in range(len(exp.hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = exp.hist
        else:
            for i in range(len(hist)):
                assert hist[i] == exp.hist[i], f"{hist} vs {exp.hist}"
            new_hist = hist + ["ignore"] + exp.hist[len(hist):]
        return HistEnvVar(exp.name, new_hist, exp.type)
    
    elif isinstance(exp, Player):
        return exp

    elif isinstance(exp, And):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return And(left, right)
    
    elif isinstance(exp, Or):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Or(left, right) 

    elif isinstance(exp, Not):
        value = align_hist(exp.value, hist)
        return Not(value)
    
    elif isinstance(exp, ITE):
        condition = align_hist(exp.condition, hist)
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return ITE(condition, left, right, exp.type)

    elif isinstance(exp, Eq):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Eq(left, right) 
    
    elif isinstance(exp, Neq):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Neq(left, right) 
    
    elif isinstance(exp, Add):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Add(left, right) 

    elif isinstance(exp, Sub):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Sub(left, right) 
    
    elif isinstance(exp, Mul):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Mul(left, right) 
    
    elif isinstance(exp, Div):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Div(left, right) 
    
    elif isinstance(exp, Pow):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Pow(left, right) 
    
    elif isinstance(exp, Lt):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Lt(left, right) 
    
    elif isinstance(exp, Le):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Le(left, right) 
    
    elif isinstance(exp, Gt):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Gt(left, right) 
    
    elif isinstance(exp, Ge):
        left = align_hist(exp.left, hist)
        right = align_hist(exp.right, hist)
        return Ge(left, right) 

    else: 
        # shouldn't see any implies nor inrange at this point (CNF)
        assert False, "unexpected Exp type"


def align_tracker(tracker: Tracker, name: str, hist: List[str]) -> Tracker:
    """
    fresh instances of item and upstream as those can change in a tracker;
    value is shallowly assigned 
    """

    new_tracker: Tracker = []

    for elem in tracker:
        if len(hist) == len(elem.upstream):
            for i in range(len(hist)):
                assert hist[i] == elem.upstream[i], f"{hist} vs {elem.upstream}"
            upstream = hist + [name]
        elif len(hist) > len(elem.upstream):
            for i in range(len(elem.upstream)):
                assert hist[i] == elem.upstream[i], f"{hist} vs {elem.upstream}"
            upstream = elem.upstream
        else:
            for i in range(len(hist)):
                assert hist[i] == elem.upstream[i], f"{hist} vs {elem.upstream}"
            upstream = hist + [name] + elem.upstream[len(hist):]
        item = align_hist(elem.item, hist)
        assert isinstance(item, HistItem) or isinstance(item, HistEnvVar)
        value = align_hist(elem.value, hist)

        new_tracker.append(TrackerElem(item, value, upstream))

    return new_tracker


def prune_pest(tree: Tree):
    """ implements step 1.4 of the read me:
    find sibling nodes that have no children and identical histories (i.e. leaves), 
    delete all but
   one, and remove the player. """
    # print("prune:\n")
    # print(tree.structure())
    if len(tree.children.keys()) == 0:
        tree.player = None

    elif len(tree.children.keys()) > 1:
        seen_actions: List[str] = []
        to_delete: List[str] = []
        for child, child_tree in tree.children.items():
            # prune child tree first
            prune_pest(child_tree)
            # if it has now no children consider it for deletion
            if len(child_tree.children.keys()) == 0:
                actionAndName = child.split("(")
                assert len(actionAndName) == 2
                action = actionAndName[0]
                if action in seen_actions:
                    to_delete.append(child)
                else:
                    seen_actions.append(action)
                    tree.children[child].player = None
        
        for child in to_delete:
            del tree.children[child]
            # print("pruned")

    else:
        # there should always be at least one behavior and ignore, thus >1 children
        assert False


def generate_pest(player_smt: List[Boolean], state_tree: Tree, 
                  players: List[Player], hist: List[str], player_hist: List[Player]):
    """modifies state tree to be player enhanced and support ignore-actions  
    ensures step 1.3 of the read me"""   

    # init: player_smt = []
    #       state_tree = entire tree
    #       players = original order
    #       hist = []
    # print("\n")
    # state_tree.structure()
    # print([p.name for p in player_hist])
    # print(players[0].name)

    


    # check breaking conditions:

    # only do stuff if it's not a leaf
    if len(state_tree.children.keys()) == 0:
        return
    
    # last player-many actions in history only contain ignore nodes
    if len(hist) >= len(players):
        last_actions = hist[-len(players):]
        if all(elem == "ignore" for elem in last_actions):
            state_tree.children = dict()
            return

    # max history length has been reached
    if len(hist) >= 10:
        print("max length has been reached")
        return

    new_players = [elem for elem in players]
    current_player = new_players.pop(0)
    
    new_players.append(current_player)

    state_tree.player = current_player

    add_ignore(state_tree, hist)

    not_ignore_child = False
    to_delete: List[str] = []
    to_add: List[Tuple[str, Tree]] = []
    for child, child_tree in state_tree.children.items():
        
        if child != "ignore":
            player_const = Eq(current_player, HistEnvVar("Caller", hist+[child], ActInt()))
            child_tree.updates.append(player_const)
            player_tracker_elem = TrackerElem(HistEnvVar("Caller", hist+[child], ActInt()), current_player, hist+[child])
            child_tree.tracker.append(player_tracker_elem)

            new_smt = to_bool(player_const)
            child_tree.smt_constraints.extend(player_smt + [new_smt])

            reachable = z3.Solver().check(child_tree.smt_constraints)

            #check satisfiability
            # if unsat remove tree
            # otherwise continue
            if reachable == z3.unsat:
                to_delete.append(child)

            elif reachable == z3.unknown:
                assert False, "z3 returned unknown"
            
            else:
                not_ignore_child = True
                to_delete.append(child)
                for p in new_players:
                    child_name = child + "(" + p.name + ")"
                    to_add.append((child_name, child_tree.copy()))
                    child_players = [elem for elem in new_players]
                    child_players.remove(p)
                    generate_pest(player_smt + [new_smt], to_add[-1][1],
                                   [p] + child_players, hist + [child], player_hist + [current_player])
    for child in to_delete:
        del state_tree.children[child]
    for child, child_pest in to_add:
        state_tree.children[child] = child_pest

    # only extend ignore if there are other possible actions too. otherwise delete
    if not_ignore_child:
        # print("there are other siblings than ignore")
        child = "ignore"
        child_tree = state_tree.children["ignore"]

        player_const = Eq(current_player, HistEnvVar("Caller", hist+[child], ActInt()))
        child_tree.updates.append(player_const)
        player_tracker_elem = TrackerElem(HistEnvVar("Caller", hist+[child], ActInt()), current_player, hist+[child])
        child_tree.tracker.append(player_tracker_elem)

        new_smt = to_bool(player_const)
        child_tree.smt_constraints.extend(player_smt + [new_smt])

        reachable = z3.Solver().check(child_tree.smt_constraints)
        # print(child_tree.preconditions)

        #check satisfiability
        # if unsat remove tree
        # otherwise continue
        if reachable == z3.unsat:
            del state_tree.children[child]

        elif reachable == z3.unknown:
            assert False, "z3 returned unknown"
        
        else:
            del state_tree.children[child]
            # constraints that in an ignore sequence no player twice
            not_ignored_players = [p for p in new_players]
            i = len(hist)-1
            if i >= 0:
                while hist[i] == "ignore" and i >= 0:
                    not_ignored_players.remove(player_hist[i])
                    i = i-1
            if state_tree.player in not_ignored_players:
                # hence current player is still allowed to ignore
                # otherwise current player has already ignored in this ignore sequence
                # then no ignore is valid, has already been deleted, so nothing to do
                for p in new_players:
                    if p != current_player:
                        child_name = child + "(" + p.name + ")"
                        state_tree.children[child_name] = child_tree.copy()
                        child_players = [elem for elem in new_players]
                        child_players.remove(p)
                        generate_pest(player_smt + [new_smt], state_tree.children[child_name], \
                                    [p] + child_players, hist + [child], player_hist + [current_player])

    else:
        # print("ignore was the only child")
        del state_tree.children["ignore"]


