# Sokoban solver

A push-optimal Sokoban solver for make.fun's
`sokoban-solver-01-run-20261121` bounty. One run answers all 5 instances
of a set: it reads `/input/<id>/level.txt` (i001–i005, XSB format) and
writes `/output/<id>/solution.txt`, the player's moves in LURD
(`u`/`d`/`l`/`r`, one letter per step).

## How it solves

Every level in this competition is a 1-wide hallway plus 1–4 rooms
(3–4 boxes each, one door each). A box pushed out of a room into the
hallway can never come back, so each room is solved on its own and the
level optimum is the sum of the room optima.

1. **Decompose.** The hallway is the row the player starts in. Removing
   it splits the floor into one connected component per room, each with
   exactly one door cell.
2. **Solve each room push-optimally.** A* over pushes: a move is one
   push, and the player's walks between pushes are filled in by BFS.
   The state is the box positions plus the player's reachable region
   (canonicalised to its smallest cell, which collapses equivalent
   states). The heuristic is the minimum-cost matching of boxes to
   goals over shortest-path distances, which is admissible, so the
   first solution found uses the fewest pushes. Deadlocks are pruned
   with static analysis: corner cells, closed wall runs with no goal,
   and frozen 2×2 blocks of boxes/walls.
3. **Stitch.** Rooms are joined with hallway walks. Every room but the
   last is solved with the extra condition that the player can walk
   back out through its door; the room where that costs the most
   pushes is solved last, where it costs nothing.

## Properties

- Pure Node standard library, no dependencies, no network.
- Deterministic: no clock, no randomness — two runs write the same
  bytes. Work caps are counted in search expansions, never in seconds.
- Fast: the whole 5-instance practice set solves in about half a
  second on one CPU, far inside the 60-second wall.

## Practice result

`grade-local --driver process` on the kit's practice set:
**score 1,000,000** — every instance solved in exactly P* pushes
(13 / 16 / 29 / 47 / 60), 5000/5000 checks, L1 regrade reproduced
byte for byte.
