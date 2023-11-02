# contract2game

project to automate the modeling of a smart contract as a game

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
