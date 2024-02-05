from pest import *
from classifier import *

def case_split(tree: Tree, hist: List[str], entire_tree: Tree):
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
            case_split(child_tree, hist + [child], entire_tree)

            # KIM: take care of upstream beh.
            # KIM: repeat for preconditions

            split, upstream = is_dependent(child_tree.beh_case + child_tree.preconditions,\
                                            tree.tracker, tree.interface, hist, entire_tree)

            constr: Exp
            # what was it supposed to be

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
