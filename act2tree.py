#!/usr/bin/env python3
"""
input: json version of act specification;
       constraints on the initial state
output: a tree of possible function calls
"""
from __future__ import annotations

import json
from act_ast import *
from parse_act_2 import parse_act_json, parse_constraints_json
from state_tree import *
from pest import *
from sys import argv
from case_splitting import *
from collections.abc import Callable
from postprocessing import *
import ast

path = argv[1]

obj = json.load(open(path))


if len(argv) > 2:
       path_extra_constraints = argv[2]
       extra_obj = json.load(open(path_extra_constraints))
       extra_constraints = parse_constraints_json(extra_obj)
else: 
       extra_constraints = []

# parse json into an Act instance
act = parse_act_json(obj)

act.to_cnf()

players_string : str = input("Input players as list of strings according to precedence. E.g ['A','B'].\n")

players_raw: List[str] = ast.literal_eval(players_string)
players: List[Player] = []
for elem in players_raw:
       players.append(Player(elem, []))


#############################################################################################################################
# USER DEFINED START

# utility_fct: UtilityFn
def utility_fct(hist: List[Tuple[str,Player]], tracker: Tracker) -> Dict[str, Exp]:

       uP: Exp = Sub( Lit(0, ActInt()), Lit("gas", ActInt())) # if it doesn't work try making "gas" a Var instead of a Lit
       uC: Exp = Lit(0, ActInt())
       uA: Exp = Lit(0, ActInt())
       utility = {players[0].name: uP , players[1].name: uC, players[2].name: uA}


       for player in players:
              for elem in hist:
                     if elem[1] == player and elem[0] != "ignore":
                            # assuming hist has the chosen action+ the player who called it not the chosen action + the next player
                            utility[player.name]= Sub(utility[player.name], Lit("gas", ActInt())) # if it doen't work try making "gas" a Var instead of a Lit

       # possible issue here: player names in history actions vs no player names in history actions (double check) for just_hist and histories in the tracker
       # if one has player names the other not, split the ones with player names on "(" to get the history without
       just_hist: List[str] = [elem[0] for elem in hist]

       # assuming the state in the JSON is called "State" and 0 = proposed,
       # 1 = cancelled, 2 = accepted, 3 = executed

       #checking if at current leaf the State is "executed"
       for tracker_elem in tracker:
              if tracker_elem.item is HistItem:
                     if tracker_elem.item.loc is VarLoc:
                            # looking at State
                            if tracker_elem.item.loc.name == "State":
                                   # looking at state for correct history
                                   if tracker_elem.item.hist == just_hist:
                                          # checking if state is executed
                                          if tracker_elem.value.is_equiv(Lit(3, ActInt())):
                                                 utility[players[0].name] = Add( utility[players[0].name], Lit("alpha", ActInt()))
                                                 utility[players[1].name] = Add( utility[players[1].name], Lit("beta", ActInt()))

       # note: that is not very pleasant to write... we should improve this in the reimplementation (making it z3 bools?) or at least simplifying accesing the tracker at the current history

       # another note: how to insert preconditions on the newly introduced values?, as additional input paramter or as part of the act spec? or in an entirely different way? 

       return utility

# USER DEFINED END
#############################################################################################################################


act_trees = []
for considered_contract in act.find_maincontract():
       act_trees.append(contract2pest(considered_contract, extra_constraints, act.store, players))


# print player enhanced state trees (their structure)
for tree in act_trees:
       tree.structure()
       print("\n")

# apply case splitting algorithm to all trees
for tree in act_trees:
       _ = case_split(tree, [], tree, players)
       print("\n")
       print("case splitting done")
       print("\n")
       tree.structure()
       print("\n")

# apply player pruning to all trees
for tree in act_trees:
       player_pruning(tree, [], players)
       print("\n")
       print("player pruning done")
       print("\n")
       tree.structure()
       print("\n")

# TODO: enable user to provide honest history and utility function here
hon_hist_string : str = input("Input honest histories as list of list of strings. E.g [['l','r'],['l','l']].\n")
honest_histories: List[List[str]] = ast.literal_eval(hon_hist_string)
assert (isinstance(honest_histories, list))
assert(all([isinstance(elem, list) for elem in honest_histories]))
assert([all(isinstance(action, str) for elem in honest_histories for action in elem)])

# utility_fct


# post-processing: compute utilities, collect constraints, generate json game tree
assert len(path.split(".json")) > 0, "unexpected file extension"  
output_name : str = path.split(".json")[0]
i : int = 1
for tree in act_trees:
       store_json(tree, utility_fct, players, honest_histories, output_name, str(i))
       i = i + 1