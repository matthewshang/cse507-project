import itertools
from z3 import *

# A Slice is a rectangular grid representing Life state at a specific time.
Slice = list[list[ExprRef]]

def make_life(solver: Solver, grid_size: int, time_steps: int) -> list[Slice]:
    """Create a (time steps) x (grid size) x (grid size) array of symbolic variables.

    Variables are named following the convention:
    "s_{t}_{i}_{j}", where t is the time step, i is the row, and j is the column.

    Args:
        solver (Solver): The Solver instance to add assertions and variables to.
        grid_size (int): The side-length of the grid to generate.
        time_steps (int): The number of time-steps to generate

    Returns:
        list[Slice]: _description_
    """
    # (tenzin): Note at some point we can potentially replace `Int`'s with `Bool`'s and instead use Z3
    # Pseudo-boolean constraints for counting boolean cardinality:
    # https://microsoft.github.io/z3guide/docs/logic/propositional-logic/#pseudo-boolean-constraints
    vars = [[[Int(f's_{t}_{i}_{j}') for j in range(grid_size)] for i in range(grid_size)] for t in range(time_steps)]

    for t in range(0, time_steps):
        for i, j in itertools.product(range(grid_size), range(grid_size)):
            # Each cell is either 0 or 1.
            solver.add(Or(vars[t][i][j] == 0, vars[t][i][j] == 1))

            if t == 0:
                continue

            # Life rules.
            count = 0
            for di, dj in itertools.product(range(-1, 2), range(-1, 2)):
                if di == dj == 0:
                    continue
                if 0 <= i + di < grid_size and 0 <= j + dj < grid_size:
                    count += vars[t - 1][i + di][j + dj]
            prev = vars[t - 1][i][j]
            next = vars[t    ][i][j]
            solver.add(Implies(And(prev == 1, next == 0), Or(count < 2, count > 3)))
            solver.add(Implies(And(prev == 1, next == 1), Or(count == 2, count == 3)))
            solver.add(Implies(And(prev == 0, next == 1), count == 3))
            solver.add(Implies(And(prev == 0, next == 0), count != 3))
    return vars

def print_model(model: ModelRef, state: list[Slice]) -> None:
    """Pretty print the model for the given state."""
    for t, s in enumerate(state):
        print(f"t = {t}")
        for i in range(len(s)):
            for j in range(len(s[0])):
                print(model[state[t][i][j]], end=" ")
            print()
        print()

def constrain(solver: Solver, s: Slice, on: set[tuple[int, int]]):
    """Constrain the given slice to be on at the given coordinates."""
    for i in range(len(s)):
        for j in range(len(s[0])):
            if (i, j) in on:
                solver.add(s[i][j] == 1)
            else:
                solver.add(s[i][j] == 0)


