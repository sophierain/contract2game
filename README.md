# contract2game

This tool uses the checkmate tool to verify game theoretic properties over an act specification.

Users must provide:

- an act specification
- a set of players
- a utility function
- a set of "honest" plays

The tool will then attempt to verify two properties:

1. All players following the "honest" path will never lose money if another player deviates
2. It is not possible for a subset of players to collectively profit by deviating

## Internals

An act specification is an abstract description of an evm program as a state transition system.

## State Tree -> Game Tree

A state tree is an internal structure that represents all possible behaviour applications to some
initial state.

```solidity
contract C {
  address x;
  uint v;
  bool c;
  bool d;

  constructor() {
    x = address(0);
    v = 0;
    c = false;
    d = false;
  }

  function f(address a) public {
    require(!c);
    c = true;
    x = a;
  }
  function g() public {
    require(x == msg.sender);
    require(c);
    require(!d);
    d = true;
    v = 100;
  }
}
```

```
         ┌───┐   0.x = 0
         │ 0 │   0.c = false
         └─┬─┘   0.d = false
           │     0.v = 0
           │
       f(a)│
           │
           │
         ┌─▼─┐  1.x = f.a
         │ 1 │  0.c = false
         └─┬─┘  1.c = true
           │
           │
           │
       g() │
           ▼
         ┌───┐  1.x = g.msg.sender
         │ 2 │  1.c = true
         └───┘  1.d = false
                2.d = true
                2.v = 100

```


## Game Tree

A game is an EFG. Each leaf in the game tree has a ulilty. Each inner node has a player, and edges
representing possible actions for that player in this stage of the game. It can have global
preconditions over variables in the utlities. Variables in the utlities have a global scope.
Preconditions cannot speak about environment variables cannot speak about players or actions.

Properties of a good game tree:

1. we have a leaf in the tree for all possible end states (negation of disjunction of the conditions for all leaves is unsat)
2. we have an edge in the tree for all possible actions (we applied all possible actions at every node, so we should have all possible edges)
3. the tree encodes all possible turn orders
4. every edge in the game tree must be executable (i.e. all conditions at each node must be always true, or depend on values under the control of the player)
5. each node in the tree has > 1 choice

## Building the Tree

### defining utilities

user provided function from state variables -> integer expression

### concretizing the turn order

Each node in the game tree must have a specific player assigned. A player is conceptually equivalent to an EVM address.
The state tree is a more compact representation where the set of potential players at each node is implied by constraints over msg.sender (TODO: maybe others? do we need to forbid constraints over e.g. tx.origin, block.coinbase?).
In order to move from a state tree to a game tree we need to discover all possible permutations of turn orderings. This can only be defined if we have a predefined set of players.

1. user provides a set of players (e.g. [`A`, `B`])
2. for each node in the state tree, discover the set of potential callers (TODO: how? with smt?)

```
         ┌───┐
         │ 0 │ callers: {address(A), address(B)}
         └─┬─┘
           │
           │
       f(a)│
           │
           │
         ┌─▼─┐
         │ 1 │ callers: {f.a}
         └─┬─┘
           │
           │
           │
       g() │
           ▼
         ┌───┐
         │ 2 │
         └───┘
```

3. unroll the state tree. in this step we replace all references to msg.sender with the address of a
   specific player. If msg.sender could have multiple values, we add a new subtree for each possible value.

```
     ┌───┐
     │ 0 │ B  ───────────────────┬──────────────────────────────┐
     └─┬─┘                       │                              │
       │                         │                              │
       │                         │                              │
   f(A)│                     f(B)│                          f(a)│
       │                         │                          a/={A,B}
       │                         │                              │
     ┌─▼─┐                     ┌─▼─┐                          ┌─▼─┐
   A │ 1 │                   B │ 1 │                          │ 1 │
     └─┬─┘                     └─┬─┘                          └───┘
       │                         │
       │                         │
       │                         │
   g() │                     g() │
       ▼                         ▼
     ┌───┐                     ┌───┐
     │ 2 │                     │ 2 │
     └───┘                     └───┘
```

  - eliminating conditions involving msg.sender
  - unrolling state tree

### adding ignore nodes

it is always a valid play to do nothing.

- payoffs for internal nodes

### add subtrees after ignore nodes

maybe repeat

### add sibling nodes with "negated preconditions"

in the above example can B behave in such a way that A cannot call g? (that is not related to msg.senders). Could be a specific value that is set in f and required in g

e.g. in closing: did A propose an honest split or a dishonest one? B can only call 'revoke' if it was dishonest

### compute utilities at each leaf

according to what user provided as input.
Some rules for that:

- utility has to depend only on history of called functions and storage values (?)
- new variables are allowed to be introduced as infinitesimals only

### deal with remaining constraints

to ensure that all available actions are always possible for the current player, the remaining constraints in the states will be first broken into CNF (conjunctive normal form) and then

1. collected as the preconditions, if they occurring varibales appear in the utilities. That requires the constraint to only contain utility variables and constants

2. collected as assumptions of the model as text, for all other constraints. E.g. the balance of each player is high-enough. If interesing, another game model with different assumptions could be generated as well.

```
         ┌───┐   0.x = 0
         │ 0 │   0.c = false
         └─┬─┘   0.d = false
           │     0.v = 0
           │
       f(a)│
           │
           │
         ┌─▼─┐  1.x = f.a
         │ 1 │  0.c = false
         └─┬─┘  1.c = true
           │    1.d = 0.d
           │    1.v = 0.v
           │
       g() │
           ▼
         ┌───┐  1.x = g.msg.sender
         │ 2 │  1.c = true
         └───┘  1.d = false
                2.d = true
                2.v = 100
                2.c = 1.c
                2.x = 1.x
```

### Constraint Kinds

preconditions:

- 1.c = true --> non dependant precondition (previous state with literals only)
- 1.x = g.msg.sender --> dependant precondition (previous state with local var)

updates:

- 2.d = true --> pure constant assignment (post state with literals only)
- 1.x = f.a --> pure variable assignment (post state with local var)
- 2.c = 1.c --> no change (equality between the same var in the pre and post)

state variable invariant:

States are collections of constraints. Applying a behaviour to a state produces a new state with new constraints.
Each storage variable of a given state (e.g. all 2.* in state 2) occurs only once in a single constraint in the constraints associated with that state.
This constraint has an update kind (i.e. pca, pva, nc).
TODO: this might need moditication if we start to consider ensures / invariants)

### Case Splitting and Dependant Preconditions

Terminology:

- dependant behaviour: a beahviour that contains a dependant precondition.
- upstream behaviour: the behaviour that can control the storage variables referenced in the dependant precondition of the dependant behaviour

If we have dependant preconditions in our constraint system, then the caller of the upstream
behaviour will be able to influence whether or not the dependant behaviour succeeds. In order to
represent this in the game tree, we will need to split the upstream behaviour accordingly.

we need to split the upstream behaviour into the case where the depdendant precondition is sat and the one where it is not.

TODO: we need to think about what happens with multiple dp, and dp involving msg.sender, also for
non neighbor upstream/dependant pairs, also dependant preconditions that have multiple upstream
behaviours.


we are looking for constraints on the local variables of the upstream that will make the dependant pc always true (or false?).
we can find the variables that will be in these constraints by walking back up the dependency graph.
e.g. we have 1.x = g.msg.sender, we look for the update involving 1.x in the constraints of f, we 1.x = f.a, since f.a is local to f, we're done.

now we have two cases to consider:

1. the upstream variable is under the control of the caller of the upstream behaviour (e.g. function args). We now split the upstream behaviour into two cases:
   1. the upstream is called in a way that makes the dp true -> e.g. add 1.x = g.msg.sender to the constraint system
   2. the upstream is called in a way that makes the dp false -> e.g. add 1.x /= g.msg.sender

2. the upstream variable is not under the control of the caller (e.g. block.coinbase, other env vars). These conditions will be made preconditions of the model.



```
# constructor
0.x = 0      # pca
0.c = false  # pca
0.d = false  # pca
0.v = 0      # pca

# f
0.c = false  # ndp
1.x = f.a    # pva
1.c = true   # pca
1.d = 0.d    # nc
1.v = 0.v    # nc

# g
1.c = true   # ndp
1.d = false  # ndp
1.x = g.msg.sender # dp
2.d = true   # pca
2.v = 100    # pca
2.c = 1.c    # nc
2.x = 1.x    # nc
```

- defined the players
- picked a starting player

1. start at the root, for each behaviour:
  - apply the beahviour, and set msg.sender to be the starting player
  - discard any new states that are always unsat

2. for each new state:
  - for each player:
    - for each behaviour:
      - apply the behaviour, and set msg.sender to be the starting player
      - check the new state for dependant preconditions
      - if they exist, apply split the upstream behaviour if needed
      - discard any new states that are always unsat

keep running 2. until the only behaviour that can be applied is ignore.

3. It may be that the case splitting in 2. produces overlapping cases (e.g. call f with a == A, call f with a /= A, call f with a == B, call f with a /= B). For each pair of constraints We consider the following cases:
     1. no overlap. the conjunction of the cases is unsat (e.g. a == A, a == B)
     2. overlap. we ask the smt solver if the second constraint is implied by the first.
       1. they do: (e.g. a == B, a /= A):
          1. the first is also implied by the second: they are the same, so we can drop one.
          2. the first is not implied by the second: add the negation of the first to the second. new pair is: (a == B, a /= A && a /= B)
       2. they do not: (e.g. a /= A, a /= B):
          1. the first is not implied by the second: skip and hope it gets rewritten in the future
          2. the first is implied by the second: add the negation of the second to the first

overlaps occur when one case implies another:
while this is true, rewrite the implied one to exclude the implicator
(a == A, a /= A) -> do nothing
(a == A, a == B) -> do nothing
(a == A, a /= B) -> rewrite all a /= B to a /= A && a /= B
(a /= A, a == B) -> rewrite all a /= A to a /= B && a /= A
(a /= A && a /= B, a /= B && a /= A) -> rewrite all a /= B && a /= A to a /= A && a /= B
(a == B, a /= B && a /= A) -> do nothing

final unique constraint set is:

a == A
a == B
a /= A && a /= B

3. apply the utility function to every leaf node

4. we have a game tree! :)

```
                        ┌───┐
                        │ A ├───────────────────────┬──────────────────────────────┬───────────────────┐
                        └─┬─┘                       │                              │                   │
                          │                         │                              │                   │
                          │                         │                              │                   │ ignore
                      f(A)│                     f(B)│                          f(a)│                   │
                          │                         │                          a/={A,B}                │
                          │                         │                              │                   │
          ignore        ┌─▼─┐                     ┌─▼─┐  ignore                  ┌─▼─┐               ┌─▼─┐
        ┌───────────────┤ A │                     │ B ├────────┐                 │   │               │ B ├───────────────────────┬──────────────────────────────┬──────────────────────────┐
        │               └─┬─┘                     └─┬─┘        │                 └───┘               └─┬─┘                       │                              │                          │
        │                 │                         │          │                                       │                         │                              │                          │
        │                 │                         │          │                                       │                         │                              │                          │
        │                 │                         │          │                                   f(A)│                     f(B)│                          f(a)│                          │ ignore
        │             g() │                     g() │          │                                       │                         │                          a/={A,B}                       │
        ▼                 ▼                         ▼          ▼                                       │                         │                              │                          │
      ┌───┐             ┌───┐                     ┌───┐      ┌───┐                         ignore    ┌─▼─┐                     ┌─▼─┐  ignore                  ┌─▼─┐                      ┌─▼─┐
      │   │             │   │                     │   │      │   │                       ┌───────────┤ A │                     │ B │ ───────┐                 │   │                      │   │
      └───┘             └───┘                     └───┘      └───┘                       │           └─┬─┘                     └─┬─┘        │                 └───┘                      └───┘
                                                                                         │             │                         │          │
                                                                                         │             │                         │          │
                                                                                         │             │                         │          │
                                                                                         │         g() │                     g() │          │
                                                                                         ▼             ▼                         │          ▼
                                                                                       ┌───┐         ┌───┐                     ┌─┴─┐      ┌───┐
                                                                                       │   │         │   │                     │   │      │   │
                                                                                       └───┘         └───┘                     └───┘      └───┘
```
