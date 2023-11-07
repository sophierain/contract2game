# contract2game

This tool uses the checkmate tool to verify game theoretic properties over an act specification.

Users must provide:

- an act specification
- a set of players and an ordering between them
- a utility function
- a set of "honest" plays

The tool will then attempt to verify two properties:

1. All players following the "honest" path will never lose money if another player deviates
2. It is not possible for a subset of players to collectively profit by deviating

## Internals

### Act Specifications

An act specification is an abstract description of an evm program as an inductive state transition
system over the integers. A spec for a contract is made up of a single constructor spec and zero or
more behaviours. Each constructor and behaviour spec is a structured collection of constraints over
the pre/post state, environment variables and calldata arguments.

### Game Tree

A game tree represents an Extensive Form Game (EFG). Each leaf in the game tree has a utility. Each
inner node has a player, and edges representing possible actions for that player in this stage of
the game. It can have global preconditions over variables in the utilities. Variables in the utilities
have a global scope. Preconditions cannot speak about players or actions.

Properties of a good game tree:

1. we have a leaf in the tree for all possible end states (negation of disjunction of the conditions for all leaves is unsat)
2. we have an edge in the tree for all possible actions (we applied all possible actions at every node, so we should have all possible edges)
3. the tree encodes all possible turn orders
4. every edge in the game tree must be executable (i.e. all conditions at each node must be always true, or depend on values under the control of the player)
5. each node in the tree has > 1 choice



### Building the Game Tree - Overview

There are a few difficulties in moving from an act specification to a game tree:

1. The act spec is inductive and potentially infinite, whereas the game tree has a fixed number of
   turns and must be finitely sized.
2. The caller in act specs is kept completely abstract, whereas in the game tree each node must
   have a concrete player assigned. This means that we have to lift constraints in the act specs
   that discuss e.g. msg.sender into the structure of the resulting game tree.
3. Every edge in the game tree must be executable, this is not something that can be guaranteed for
   an arbitrary composition of behaviours in act. Since each behaviour has preconditions that may
   depend on values set in a previous behaviour, we sometimes need to generate multiple edges in
   the game tree for a single act behaviour.
4. It is always a valid play in any game to do nothing. The game tree should therefore contain
   "ignore" edges which are not present in the act specification.
5. The game tree has a global namespace for variables, and only admits global preconditions at the
   root of the tree. Act specifications can have local variables and behaviour local constraints. We
   must therefore lift all constraints to the root of the tree and apply variable renaming to mimic
   this local variable and constraint scoping.
6. The game tree is defined over the reals, and the act specification is defined over ints. This is
   mostly a safe over abstraction (see section for arguments), but is unsound for expressions
   involving division.

In order to construct the game tree we need the following steps:

- build (player enhanced) state tree (with ignore)
  - assign a player to each node
  - add ignore edges to every node
  - produces a state tree
- case splitting
  - constraint classification
  - caller dependent case splits
  - history dependent case splits
    - ensures that every action is always executable by the player
  - case consistency transformations
    - rewrite case conditions to ensure that they are both exhaustive and non overlapping
- apply utilities
  - apply payoff function to produce utilites at each leaf node
- lift constraints & variable renaming

### build (player enhanced) state tree (with ignore)

- defined the players
- picked a starting player

1. start at the root, for each behaviour (including ignore):
    - apply the behaviour, and set msg.sender to be the starting player
    - discard any new states that are always unsat

2. for each new state:
    - for each player:
        - for each behaviour (including ignore):
            - apply the behaviour, and set msg.sender to be the current player
            - discard any new states that are always unsat

keep running 2. until any of the following stop conditions is true:

- the only behaviour that can be applied is ignore
- the history contains only ignore edges, and every player has played ignore once
- a max history length has been reached

### Case Splitting

#### Constraint Classification

Game tree construction requires different steps depending on the "kind" of constraints that are
present at a given state. We need to find constraints that involve variables that are under the
control of players from previous steps (dependent precondtions), within this subset of constriants,
there are two kinds of constriant that we are interested in:

1. Constraints involving msg.sender (caller dependent preconditions)
2. Constraints involving state variables that can be influenced by a previous call (history dependent preconditions)

We therefore need two classifiers:

##### General Dependency Classifier

This classifier uses the smt solver to tell us if a given constraint can always be made true by
setting player controlled variables only. For each constraint we construct the following formula and
check it's satisifiability in z3:

```
exists (iface vars + msg.value) . forall (others) . constraint
```

This will return sat iff the truth value of the constraint depends only on player controlled
variables.

##### Caller Dependency

All dependent constraints require some case splitting, but the exact form depends on whether the
constraint talks about msg.sender. We implement a very simple fully static classifier that first
checks if msg.sender is present in the constraint at all. If it is not, then it is a history
dependent precondition, if it is then it is potentially caller dependent.

We then analyze the potentially caller depedent constraints. This stage is currently extremely
simple and simply rejects constraints that are not disjunctions of simple (in-)equalities between
msg.sender and a single term (either a literal or a variable).

We need this because the dependent constraint may be dependent on many variables, and we don't know
how to split constraints depend on msg.sender and other variables (and these constraints are anyway
rather esoteric and unlikely to occur in normal code). We therefore support only this very simple
form of msg.sender constraint, and expect that to be enough for most real world code.


#### Caller Dependent Case Splits

Terminology:

- dependant behaviour: a beahviour that contains a player dependant precondition (pdp).
- upstream behaviour: the behaviour that can control the storage variables referenced in the pdp of the dependant behaviour

If we have pdps in our constraint system, then the caller of the upstream behaviour will be able to
influence whether or not the dependant behaviour succeeds. In order to represent this in the game
tree, we will need to split the upstream behaviour accordingly.

we need to split the upstream behaviour into the case where the pdp is sat and the one where it is not.

TODO: we need to think about what happens with multiple dp, and dp involving msg.sender, also for
non neighbor upstream/dependant pairs, also dependant preconditions that have multiple upstream
behaviours.

we are looking for constraints on the local variables of the upstream that will make the dependant pc always true (or false?).
we can find the variables that will be in these constraints by walking back up the dependency graph.
e.g. we have 1.x = g.msg.sender, we look for the update involving 1.x in the constraints of f, e.g. 1.x = f.a, since f.a is local to f, we're done.

now we have two cases to consider:

1. the upstream variable is under the control of the caller of the upstream behaviour (e.g. function args). We now split the upstream behaviour into two cases:
   1. the upstream is called in a way that makes the dp true -> e.g. add 1.x = g.msg.sender to the constraint system
   2. the upstream is called in a way that makes the dp false -> e.g. add 1.x /= g.msg.sender

2. the upstream variable is not under the control of the caller (e.g. block.coinbase, other env vars). These conditions will be made preconditions of the model.


##### identifying the upstream behaviour

once we know all the dependent constraints (both caller and history) from the classifier, we focus first on the caller dependent constraints:

we know the constraint has the following shape: history.storage_var = (!=) behv.msg.sender or history.other_stor_var = (!=) behv.msg.sender or...
hence we collect all the LHS that occur.

if LHS is a storage_var keep the storage var
if LHS is a function evaluation stor_fun(var) where stor_fun is a function in the storage and var any type of variable or numeric value keep both

In the state storage tracker (TO CONSIDER IN THE WRITE-UP) we look up all the mentioned entires and which previous behaviours accesses them (only the relevant ones --> if new sth assigned all prev dependencies removed)

split on the upstream behv s.t. the dependent behv is sat in one branch and usat in the other



#### History Dependant Case Splits

#### Case Consistency Transformations

3. It may be that the case splitting in 2. produces overlapping cases (e.g. call f with a == A, call f with a /= A, call f with a == B, call f with a /= B). For each pair of constraints We consider the following cases:
     1. no overlap. the conjunction of the cases is unsat (e.g. a == A, a == B)
     2. overlap. we ask the smt solver if the second constraint is implied by the first.
       1. they do: (e.g. a == B, a /= A):
          1. the first is also implied by the second: they are the same, so we can drop one.
          2. the first is not implied by the second: add the negation of the first to the second. new pair is: (a == B, a /= A && a /= B)
       2. they do not: (e.g. a /= A, a /= B):
          1. the first is not implied by the second: skip and hope it gets rewritten in the future
          2. the first is implied by the second: add the negation of the second to the first

### Safety of Integer -> Real Conversion

We think that this is a sound over abstraction for all arithmetic ops except division.

TODO: document our reasoning.

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
         ┌─▼─┐  0.c = false
         │ 1 │  1.x = f.a
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
                2.x = 1.x
                2.c = 1.c

```

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

- state remains unchanged

### add subtrees after ignore nodes

maybe repeat

### add sibling nodes with "negated preconditions"

in the above example can B behave in such a way that A cannot call g? (that is not related to msg.senders). Could be a specific value that is set in f and required in g

e.g. in closing: did A propose an honest split or a dishonest one? B can only call 'revoke' if it was dishonest

### compute utilities at each leaf

according to what user provided as input.
Some rules for that:

- utility has to depend only on history of called functions and storage values (keep track of those in an additional data structure?)
- new variables are allowed to be introduced as infinitesimals only

### deal with remaining constraints

to ensure that all available actions are always possible for the current player, the remaining constraints in the states will be first broken into CNF (conjunctive normal form) and then

1. collected as the preconditions, if the occurring variables appear in the utilities. That requires the constraint to only contain utility variables and constants

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

### Case Splitting and Dependant Preconditions

Terminology:

- dependant behaviour: a beahviour that contains a dependant precondition.```
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
   1. the upstream is called in a way that makes the dp true -> e.g. add 1.x = g.msg.sender to the constraint system```
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

1. start at the root, for each behaviour (including ignore):
  - apply the behaviour, and set msg.sender to be the starting player
  - discard any new states that are always unsat

2. for each new state:
  - for each player:
    - for each behaviour:
      - apply the behaviour, and set msg.sender to be the current player
      - check the new state for dependant preconditions
      - if they exist, split the upstream behaviour if needed
      - discard any new states that are always unsat

keep running 2. until the only behaviour that can be applied is ignore.

3. It may be that the case splitting in 2. produces overlapping cases (e.g. call f with a == A, call f with a /= A, call f with a == B, call f with a /= B). For each pair of constraints We consider the following cases:
     1. no overlap. the conjunction of the cases is unsat (e.g. a == A, a == B)
     2. overlap. we ask the smt solver if the second constraint is implied by the first.
       1. they do: (e.g. a == B, a /= A):
          1. the first is also implied by the second: they are the same, so we can drop one.
          2. the first is not implied by the second: add the negation of the first to the second. new pair is: (a == B, a /= A && a /= B)
       2. they do not: (e.g. a /= A, a /= B):```

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
