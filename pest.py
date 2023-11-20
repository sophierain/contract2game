from act_ast import Exp
from state_tree import *




def contract2pest(contract: Contract, extra_constraints: List[Exp], \
                  store: Storage, players: List[Player]) -> Tree:

    state_tree = contract2tree(contract, extra_constraints, store)
    assert len(players) > 1, "at least 2 players required"

    new_players = [elem for elem in players]
    current_p = new_players.pop[0]
    new_players.append(current_p)
    state_tree.player = current_p

    add_ignore(state_tree) # adds ignore branch and copies entire tree there 
    

    for child, tree in  state_tree.items():
        generate_pest(tree, new_players, [], child)

    prune_pest(state_tree)


def add_ignore(tree: Tree):
    """ add ignore branch
    ensures step 1.3 of the read me
    """
    pass

def prune_pest(tree: Tree):
    """ implements step 1.4 of the read me"""
    pass

def generate_pest(state_tree: Tree, players: List[Player], hist: List[str], name: str):
    """modifies state tree to be player enhanced and support ignore-actions"""    
    # new_players = [elem for elem in players]
    # current_p = new_players.pop[0]
    # new_players.append(current_p)
    # state_tree.player = current_p
    prev_p = players[-1]
    player_const = Eq(prev_p, HistEnvVar("Caller", hist, ActInt()))
    state_tree.preconditions.append(player_const)

    #check satisfiability
    # if unsat remove tree
    # otherwise continue

    add_ignore(state_tree)

    for p in players:
        new_players = [elem for elem in players]
        new_players.remove(p)
        new_players.append(p)
        for child, tree in  state_tree.items():
            generate_pest(tree, new_players, hist + [name], child)






