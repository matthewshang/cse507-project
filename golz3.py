import itertools
import z3

# A Slice is a rectangular grid representing Life state at a specific time.
Slice = list[list[z3.ArithRef]]


# A Concrete Slice (i.e.: a slice where the values are concrete).
ConcSlice = list[list[int]]

def make_life(solver: z3.Solver, grid_size: int,
              time_steps: int) -> list[Slice]:
    """
    Create a (time steps) x (grid size) x (grid size) array of symbolic variables
    representing a Game of Life board of size grid_size across time_steps time
    steps.

    The variables in each time step are constrained such that slice at time i
    leads to the board state at time i + 1 (where we assume all cells outside of
    the region of interest are dead).

    Variables are named following the convention:
    "s_{t}_{i}_{j}", where t is the time step, i is the row, and j is the column.

    Args:
        solver (Solver): The Solver instance to add assertions and variables to.
        grid_size (int): The side-length of the grid to generate.
        time_steps (int): The number of time-steps to generate

    Returns:
        list[Slice]: A list of Slice's, where list[i] represents the i'th timestep (larger i ==> later
          in time). Use this to reference the symbolic variables when constraining or accessing.
    """
    vars = [[[z3.Int(f's_{t}_{i}_{j}') for j in range(grid_size)]
             for i in range(grid_size)] for t in range(time_steps)]

    for t in range(0, time_steps):
        for i, j in itertools.product(range(grid_size), range(grid_size)):
            from z3 import Or, And, Implies, Not
            # Each cell is either 0 or 1.
            solver.add(Or(vars[t][i][j] == 0, vars[t][i][j] == 1))

            if t == 0:
                continue

            # Life rules.
            # `count` symbolically counts the number of alive neighbors cell[i][j] has.
            count = 0
            for di, dj in itertools.product(range(-1, 2), range(-1, 2)):
                if di == dj == 0:
                    continue
                if 0 <= i + di < grid_size and 0 <= j + dj < grid_size:
                    count += vars[t - 1][i + di][j + dj]
            prev = vars[t - 1][i][j]
            next = vars[t][i][j]
            count_2 = count == 2
            count_3 = count == 3
            lhs = next == 1
            rhs = Or(And(prev == 1, Or(count_2, count_3)),
                     And(prev == 0, count_3))
            solver.add(lhs == rhs)

    return vars


def print_model(model: z3.ModelRef, state: list[Slice]) -> None:
    """Pretty print the model for the given state."""
    for t, s in enumerate(state):
        print(f"t = {t}")
        for i in range(len(s)):
            for j in range(len(s[0])):
                print(model[state[t][i][j]], end=" ")
            print()
        print()


def constrain(solver: z3.Solver, s: Slice, on: set[tuple[int, int]]):
    """Constrain the given slice to be on at the given coordinates."""
    for i in range(len(s)):
        for j in range(len(s[0])):
            if (i, j) in on:
                solver.add(s[i][j] == 1)
            else:
                solver.add(s[i][j] == 0)


def constrain_life_boundary(solver: z3.Solver, state: list[Slice]):
    """
    Strictly enforce that the solver doesn't choose a configuration that would lead
    to any cells outside of the region of interest being set to 1.

    Because we assume that all cells outside the region of interest in the predecessor
    are 0, this constraint is necessary to guarantee a correct answer when doing
    predecessor queries with more than one time transition (although with one it's
    fine as we can just assert then that the predecessor's border cells are dead
    for free).

    Args:
        solver (Solver): Z3 Solver to add constraints to.
        state (list[Slice]): The Game of Life variables represented as slices over time.
            state[time][row][col] should be var for cell at time, row, col.
    """
    # We don't actually assert for the corners or boundary cells adjacent to corners,
    # since they can only have at most 2 neighbors in the region of interest, and thus
    # can't come alive.
    # e.g.: region of interest marked with x's, 0 are boundary cells we don't need
    # to consider, V are boundary cells we do.
    # 0 0 V 0 0
    # 0 x x x 0
    # V x x x V
    # 0 x x x 0
    # 0 0 V 0 0

    # For a V to not come alive all that's strictly necessary is that the 3 x's it's
    # adjacent to aren't ALL 1's, or equivalently: at least one of them is 0.
    # Which encoding is more efficient?

    # Get num rows to determine size. We assume it's square.
    size = len(state[0])

    # For each predecessor timestep assert state wouldn't be such that any boundary
    # cells come alive.
    for t in range(0, len(state) - 1):
        s = state[t]
        # Do top row and bottom row
        for col in range(1, size - 1):
            # Top row
            solver.add((s[0][col - 1] + s[0][col] + s[0][col + 1]) != 3)
            # Bottom row
            solver.add((s[size - 1][col - 1] + s[size - 1][col] +
                        s[size - 1][col + 1]) != 3)

        # Do left and right sides
        for row in range(1, size - 1):
            # Left
            solver.add((s[row - 1][0] + s[row][0] + s[row + 1][0]) != 3)
            # Right
            solver.add((s[row - 1][size - 1] + s[row][size - 1] +
                        s[row + 1][size - 1]) != 3)


def model_to_python(model: z3.ModelRef,
                    state: list[Slice]) -> list[list[list[int]]]:
    """
    Convert a model for sequence of Game of Life states to a native python
    3D-list of integers where each int represents cell state at given time.

    list[time][row][col] gives the cell state of cell at row,col at given timestep.

    Args:
        model (ModelRef): Model of states.
        state (list[Slice]): State variables organized s.t. state[time][row][col]
            gives reference for Z3 variable representing cell at given time, row, and
            column.

    Returns:
        list[list[list[int]]]: list[time][row][col] gives the cell state of cell
            at row,col at given timestep, but in Python native form :sunglasses:.
    """
    return [[[model[var].as_long() for var in row] for row in slice]
            for slice in state]  # type: ignore
