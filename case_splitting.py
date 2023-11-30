from pest import *
from classifier import *

def case_split(tree: Tree):
    """
    go through the tree probs bottom up and check whether splitting is required.
    if so, adapt name of branch and add new ones acc. to case split
    if not proceed to next node
    """

    if tree.player == None:
        # leaf case
       return

    else:
        for child in tree.children:
            # call recursion first to proceed bottom up
            case_split(child)

            # KIM: take care of upstream beh.
            # KIM: repeat for preconditions
            for constr in child.beh_case:
                split, upstream = is_dependent(constr, tree.tracker, tree.interface)
                if split:
                    if caller_dep(constr, tree.tracker):
                        caller_split(tree, child, constr, upstream)
                    else:
                        hist_split(tree, child, constr, upstream)


    return

def caller_dep(constr: Exp, tracker: Tracker) -> bool:
    pass

def caller_split(tree: Tree, child: Tree, constr: Exp):
    pass

def hist_split(tree: Tree, child: Tree, constr: Exp):
    pass