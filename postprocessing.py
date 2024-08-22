from pest import *
from collections.abc import Callable
import dsl

PLAYERS: List[dsl.Player] = []
HONEST_HISTORIES: List[List[dsl.Action]] = []

ACTIONS: List[dsl.Action] = []

CONSTANTS: List[dsl.Expr] = []
INFINITESIMALS: List[dsl.Expr] = []

INITIAL_CONSTRAINTS: List[dsl.Constraint] = []

# the specific ones stay empty as they are supposed to be a debugging feature 
WEAK_IMMUNITY_CONSTRAINTS: List[dsl.Constraint] = []
WEAKER_IMMUNITY_CONSTRAINTS: List[dsl.Constraint] = []
COLLUSION_RESILIENCE_CONSTRAINTS: List[dsl.Constraint] = []
PRACTICALITY_CONSTRAINTS: List[dsl.Constraint] = []




# called on each leaf node. takes a history of called methods and the state tracker at that leaf
# returns a utility map
UtilityFn = Callable[[List[Tuple[str,Player]], Tracker], Dict[str, Exp]]

def compute_utilities(utility_fct: UtilityFn, hist_and_player: List[Tuple[str, Player]], tracker: Tracker) -> Dict[dsl.Player, dsl.LExpr]:
    
    # KIM: add CONSTANTS and INFINITESIMALS
    utility: Dict[str, Exp] = utility_fct(hist_and_player, tracker)

    dsl_utility: Dict[dsl.Player, dsl.LExpr] = dict()

    for player, exp in utility.items():
        dsl_exp = actint2dsl(exp)
        assert not dsl_exp == None, "players should not occur in utility terms"
        for dsl_player in PLAYERS:
            if dsl_player.value == player:
                dsl_utility[dsl_player] = dsl_exp

    return dsl_utility


def store_json(tree: Tree, utility_fct: UtilityFn, players: List[Player], honest_histories: List[List[str]], output_name: str, tree_number: str):
    
    player_names = [pl.name for pl in players]
    PLAYERS.extend(dsl.players(*player_names))
    HONEST_HISTORIES.extend([[dsl.Action(elem) for elem in hon_hist] for hon_hist in honest_histories])

    game_tree = generate_game_tree(tree, utility_fct, [])

    dsl.finish(
        PLAYERS,
        ACTIONS,
        INFINITESIMALS,
        CONSTANTS,
        INITIAL_CONSTRAINTS,
        WEAK_IMMUNITY_CONSTRAINTS,
        WEAKER_IMMUNITY_CONSTRAINTS,
        COLLUSION_RESILIENCE_CONSTRAINTS,
        PRACTICALITY_CONSTRAINTS,
        HONEST_HISTORIES,
        game_tree,
        output_name,
        tree_number
    )

def generate_game_tree(tree: Tree, utility_fct: UtilityFn, hist_and_player: List[Tuple[str, Player]]) ->  dsl.Tree:
    
    game_tree: dsl.Tree
    
    # collect constraints
    INITIAL_CONSTRAINTS.extend(translate2dsl(tree.beh_case))
    INITIAL_CONSTRAINTS.extend(translate2dsl(tree.preconditions))
    INITIAL_CONSTRAINTS.extend(translate2dsl(tree.updates))
    INITIAL_CONSTRAINTS.extend(translate2dsl(tree.split_constraints))

    # for exp in tree.beh_case:
    #     print(exp)
    # for exp in tree.preconditions:
    #     print(exp)
    # for exp in tree.updates:
    #     print(exp)
    # for exp in tree.split_constraints:
    #     print(exp)


    if len(tree.children.keys()) == 0:
        # we are at a leaf, thus compute utility
        assert not tree.player, "Leaf should not have a player" 
        game_tree = dsl.leaf(compute_utilities(utility_fct, hist_and_player, tree.tracker))

    else:
        assert tree.player, "Branch should have a player"
        game_tree_children: Dict[dsl.Action, dsl.Tree] = dict()
        game_tree_player: dsl.Player | None = None

        # find player in PLAYERS
        for pl in PLAYERS:
            if pl.value == tree.player.name:
                game_tree_player = pl
        assert game_tree_player, f"player not found: current player {tree.player.name}, {[elem.value for elem in PLAYERS]}"

        for childname, child in tree.children.items():
            action = dsl.Action(childname)
            ACTIONS.append(action)
            game_tree_children[action] = generate_game_tree(child, utility_fct, hist_and_player + [(childname, tree.player)])

        game_tree = dsl.branch(game_tree_player, game_tree_children)
    
    return game_tree

def translate2dsl(exp_list: List[Exp]) -> List[dsl.Constraint]:
    res: List[dsl.Constraint] = []

    for exp in exp_list:
        dsl_exp = act2dsl(exp)
        if not dsl_exp == None:
            res.append(dsl_exp)
    
    return res

def act2dsl(exp: Exp) -> dsl.Constraint | None:
    """store only int constraints, rest is not relevant for utilities
        also constraints in which a player occurs will be discarded.
        trivial constraints will also be removed
    """

    # don't expect player, Add, sub, Mul, div, pow at top level
    assert not isinstance(exp, Player)
    assert not isinstance(exp, Add)
    assert not isinstance(exp, Sub)
    assert not isinstance(exp, Mul)
    assert not isinstance(exp, Div)
    assert not isinstance(exp, Pow)
    # don't expect Var, Envvar, Implies, ITE, inrange, storageitem at all 
    assert not isinstance(exp, Var)
    assert not isinstance(exp, EnvVar)
    assert not isinstance(exp, Implies)
    assert not isinstance(exp, ITE)
    assert not isinstance(exp, InRange)
    assert not isinstance(exp, StorageItem)

    # if literal at top level, has to be boolean --> discard
    if isinstance(exp, Lit):
        return None
    # if HistVar at top level, has to be boolean --> discard
    elif isinstance(exp, HistVar):
        return None
    # if HistEnvVar at top level, has to be boolean --> discard
    elif isinstance(exp, HistEnvVar):
        return None    
    # if HistItem at top level, has to be boolean --> discard
    elif isinstance(exp, HistItem):
        return None  
    elif isinstance(exp, And):
        left = act2dsl(exp.left)
        right = act2dsl(exp.right)
        if (not left == None) and (not right == None):
            return dsl.conjunction(left, right)
        elif (not left == None) :
            return left
        elif (not right == None) :
            return right
        else :
            return None
    elif isinstance(exp, Or):
        left = act2dsl(exp.left)
        right = act2dsl(exp.right)
        if (not left == None)  and (not right == None) :
            return dsl.disjunction(left, right)
        elif (not left == None) :
            return left
        elif (not right == None) :
            return right
        else :
            return None
    elif isinstance(exp, Not):
        value = act2dsl(exp.value)
        if value != None:
            # value is either a Conjunction or a Disjunction (neither should be the case as input should be in CNF), 
            # or DisequationConstraint --> negate those


            assert isinstance(value, dsl.DisequationConstraint)
            op : str
            if value.op == "=":
                op = "!="
            elif value.op == "!=":
                op = "="            
            if value.op == "<=":
                op = ">"
            elif value.op == ">=":
                op = "<"
            elif value.op == "<":
                op = ">="
            else:
                assert value.op == ">"
                op = "<="
            return dsl.DisequationConstraint(op, value.left, value.right)
        else: 
            return None


    elif isinstance(exp, Eq):
        if exp.left.type != ActInt():
            return None
        else: 
            # takes trivial returns into accout, if player appears or tautologies
            assert exp.right.type == ActInt()
            int_left = actint2dsl(exp.left)
            int_right = actint2dsl(exp.right)
            if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
                return dsl.DisequationConstraint("=", int_left, int_right)
            else: 
                return None
        
    elif isinstance(exp, Neq):
        if exp.left.type != ActInt():
            return None
        else: 
            # takes trivial returns into accout, if player appears or tautologies
            assert exp.right.type == ActInt()
            int_left = actint2dsl(exp.left)
            int_right = actint2dsl(exp.right)
            if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
                return dsl.DisequationConstraint("!=", int_left, int_right)
            else: 
                return None

    elif isinstance(exp, Lt):
        assert exp.left.type == ActInt()
        assert exp.right.type == ActInt()
        # takes trivial returns into accout, if player appears or tautologies
        int_left = actint2dsl(exp.left)
        int_right = actint2dsl(exp.right)
        if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
            return dsl.DisequationConstraint("<", int_left, int_right)
        else: 
            return None
        
    elif isinstance(exp, Le):
        assert exp.left.type == ActInt()
        assert exp.right.type == ActInt()
        # takes trivial returns into accout, if player appears or tautologies
        int_left = actint2dsl(exp.left)
        int_right = actint2dsl(exp.right)
        if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
            return dsl.DisequationConstraint("<=", int_left, int_right)
        else: 
            return None

    elif isinstance(exp, Gt):
        assert exp.left.type == ActInt()
        assert exp.right.type == ActInt()
        # takes trivial returns into accout, if player appears or tautologies
        int_left = actint2dsl(exp.left)
        int_right = actint2dsl(exp.right)
        if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
            return dsl.DisequationConstraint(">", int_left, int_right)
        else: 
            return None
    
    elif isinstance(exp, Ge):
        assert exp.left.type == ActInt()
        assert exp.right.type == ActInt()
        # takes trivial returns into accout, if player appears or tautologies
        int_left = actint2dsl(exp.left)
        int_right = actint2dsl(exp.right)
        if int_left != None and int_right != None and (type(int_left) != int or type(int_right) != int):
            return dsl.DisequationConstraint(">=", int_left, int_right)
        else: 
            return None

    else:
        assert False    


def actint2dsl(exp: Exp) -> dsl.LExpr | None:
    """translate terms to dsl expressions"""

    assert not isinstance(exp, Var)
    assert not isinstance(exp, EnvVar)
    assert not isinstance(exp, Implies)
    assert not isinstance(exp, ITE)
    assert not isinstance(exp, InRange)
    assert not isinstance(exp, StorageItem)
    assert not isinstance(exp, And)
    assert not isinstance(exp, Or)
    assert not isinstance(exp, Not)
    assert not isinstance(exp, Eq)
    assert not isinstance(exp, Neq)
    assert not isinstance(exp, Le)
    assert not isinstance(exp, Lt)
    assert not isinstance(exp, Ge)
    assert not isinstance(exp, Gt)

    if isinstance(exp, Player):
        return None
    elif isinstance(exp, Lit):
        assert type(exp.value) == int
        return exp.value
    elif isinstance(exp, HistVar):
        assert exp.type == ActInt()
        name = exp.to_string()
        dsl_exp = dsl.NameExpr(name)
        # if not already in CONSTANTS, has to be added
        to_add = True
        for elem in CONSTANTS:
            assert isinstance(elem, dsl.NameExpr)
            if elem.name == name:
                to_add = False
        if to_add:
            CONSTANTS.append(dsl_exp)
        return dsl_exp
    # if HistEnvVar at top level, has to be boolean --> discard
    elif isinstance(exp, HistEnvVar):
        assert exp.type == ActInt()
        name = exp.to_string()
        dsl_exp = dsl.NameExpr(name)
        # if not already in CONSTANTS, has to be added
        to_add = True
        for elem in CONSTANTS:
            assert isinstance(elem, dsl.NameExpr) 
            if elem.name == name:
                to_add = False
        if to_add:
            CONSTANTS.append(dsl_exp)
        return dsl_exp  
    # if HistItem at top level, has to be boolean --> discard
    elif isinstance(exp, HistItem):
        assert exp.type == ActInt()
        name = exp.to_string()
        dsl_exp = dsl.NameExpr(name)
        # if not already in CONSTANTS, has to be added
        to_add = True
        for elem in CONSTANTS:
            assert isinstance(elem, dsl.NameExpr)
            if elem.name == name:
                to_add = False
        if to_add:
            CONSTANTS.append(dsl_exp)
        return dsl_exp  
    
    elif isinstance(exp, Add):
        # takes trivial returns into account, if player appears 
        left = actint2dsl(exp.left)
        right = actint2dsl(exp.right)
        if left != None and right != None:
            return left + right
        else: 
            return None
      
    elif isinstance(exp, Sub):
        # takes trivial returns into account, if player appears 
        left = actint2dsl(exp.left)
        right = actint2dsl(exp.right)
        if left != None and right != None:
            return left - right
        else: 
            return None

    elif isinstance(exp, Mul):
        # takes trivial returns into account, if player appears
        left = actint2dsl(exp.left)
        right = actint2dsl(exp.right)
        if left != None and right != None:
            return left * right
        else: 
            return None
        
    elif isinstance(exp, Div):
        # takes trivial returns into account, if player appears
        left = actint2dsl(exp.left)
        right = actint2dsl(exp.right)
        assert not isinstance(left, bool)
        if left != None and right != None:
            if (not isinstance(left, dsl.Expr)) and (not isinstance(right, dsl.Expr)):
                return left / right 
            elif not isinstance(left,dsl.Expr):
                assert isinstance(right, dsl.Expr)
                return right.__rdiv__(left)
            else:
                return left.__div__(right)
        else: 
            return None
        
    elif isinstance(exp, Pow):
        # takes trivial returns into account, if player appears
        left = actint2dsl(exp.left)
        right = actint2dsl(exp.right)
        assert type(right) == int
        if left != None and right != None:
            return left ** right
        else: 
            return None
    
    else:
        assert False