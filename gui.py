"""
GUI application for submitting Game of Life queries 
"""

import tkinter
from tkinter import ttk
import itertools
from z3 import *
import golz3

# Side length in px of cells when drawn to board.
CELL_SIZE = 30


class Cell:
    """
    A single cell in the Game of Life board.

    States:
    - 0 = dead
    - 1 = alive/selected in Board
    """

    def __init__(self, state=0):
        self.state = state

    def toggle(self):
        self.state = 0 if self.state else 1


# Board offset from top and left side of canvas so that lines draw.
BOARD_OFFSET = 10


class Board:
    """
    The Game of Life board.
    """

    def __init__(self, canvas: tkinter.Canvas, size: int, bind_callbacks=True):
        """Create a new Game of Life Board.

        Args:
            canvas (Canvas): Canvas to use for drawing life board. This Board object
                takes ownership of the Board and will clear/draw to it.
            size (int): side length of grid in terms of number of cells.
            bind_callbacks (bool): if true, then bind callbacks for this Board (so it
                can be interacted with by clicking).
        """
        self.canvas = canvas
        self.size: int = size
        # 2D array of Cell objects representing the state of the board.
        self.board: list[list[Cell]] = [
            [Cell(0) for col in range(size)] for row in range(size)]

        if bind_callbacks:
            self.bind_callbacks()

        canvas.delete("all")
        self.draw()

    def draw(self) -> None:
        """
        Draw the board. Clears previous state of canvas.
        """
        self.canvas.delete("all")
        # Loop over and draw a square for each
        for row in range(self.size):
            for col in range(self.size):
                # Mysterious OFFSETs are to get grid lines to all draw (otherwise top and left side
                # of grid are cut off)
                fill = "gray26" if self.board[row][col].state else "white"
                self.canvas.create_rectangle(
                    BOARD_OFFSET + col * CELL_SIZE,
                    BOARD_OFFSET + row * CELL_SIZE,
                    BOARD_OFFSET + (col + 1) * CELL_SIZE,
                    BOARD_OFFSET + (row + 1) * CELL_SIZE,
                    fill=fill)

    def bind_callbacks(self):
        """
        Bind callbacks for clicking etc. to the provided canvas.

        This Board object now takes ownership of the provided canvas and will handle
        redrawing and updating it when necessary based off of board events.
        """
        self.canvas.bind("<Button-1>", self.on_left_click)

    def coord_to_row_col(self, x: int, y: int) -> tuple[int, int]:
        """
        Return (row,col) corresponding to given x,y coordinate.

        NOTE: row, col can be invalid (if input was invalid).
        """
        # Math must match with math in `draw()` where cells are created.
        # Note that x increases to the right ->, y increases down.
        row = (y - BOARD_OFFSET) // CELL_SIZE
        col = (x - BOARD_OFFSET) // CELL_SIZE
        return row, col

    def coord_to_cell(self, x: int, y: int) -> Cell | None:
        """
        Return the cell that contains the given (x,y) Canvas coordinate or None
        if no such cell is found.
        """
        # Math must match with math in `draw()` where cells are created.
        # Note that x increases to the right ->, y increases down.
        row, col = self.coord_to_row_col(x, y)
        if (0 <= row < self.size and 0 <= col < self.size):
            return self.board[row][col]

        # Otherwise: invalid offset.
        return None

    def get_cell_state(self, row: int, col: int) -> int:
        """
        Return the state of the cell at (row, col) in this board.

        Raises an Invalid Argument Exception if row/col are out of bounds.

        Args:
            row (int): row of cell.
            col (int): column of cell.

        Returns:
            int: the state of cell at (row, col).
        """
        if not (0 <= row < self.size and 0 <= col < self.size):
            raise ValueError(
                f"Row {row} and column {col} not within grid (grid size={self.size})")

        return self.board[row][col].state

    def set_cell_state(self, row: int, col: int, state: int):
        """
        Set the state of the Cell at (row, col) to the specified state. For
        changes to be reflected on board, board must be redrawn.

        Raises an Invalid Argument Exception if row/col are out of bounds.

        Args:
            row (int): row of cell.
            col (int): column of cell.
            state (int): new state for cell.
        """
        if not (0 <= row < self.size and 0 <= col < self.size):
            raise ValueError(
                f"Row {row} and column {col} not within grid (grid size={self.size})")

        self.board[row][col].state = state

    def set_board_state(self, state: list[list[int]]):
        """
        Set the state of the board based off of a 2D list of values.

        Raises an exception if dimensions of "state" do not match
        the dimensions of this board.

        Args:
            state (list[list[int]]): the board state to copy as this board's state.
        """
        if len(state) != self.size:
            raise ValueError("State must have have SIZE rows")

        for row in range(0, self.size):
            if len(state[row]) != self.size:
                raise ValueError(
                    f"All rows of `state` must have {self.size} rows. Row {row} of state is of length: {len(state[row])}")
            for col in range(0, self.size):
                self.board[row][col].state = state[row][col]

    def on_left_click(self, event):
        # print(f"Click at x: {event.x}, y: {event.y}", end="")

        # row, col = self.coord_to_row_col(event.x, event.y)
        # print(f" row={row}, col={col}")

        cell = self.coord_to_cell(event.x, event.y)

        if not cell:
            return

        # Flip cell from dead to alive.
        cell.toggle()

        self.draw()


WIDTH = 800
HEIGHT = 600
SIZE = 3

INPUT_DESCRIPTION = """\
Use this grid to select the desired end state. Left click on cells to mark
them as alive or dead. Once ready, use the submit button below to submit
the query for a predecessor.
""".replace("\n", " ")

OUTPUT_DESCRIPTION = """\
This grid visualizes the results of the query.
""".replace("\n", " ")


class App:
    """
    Top level application
    """

    def __init__(self):
        # (tenzin): Copying a good part of the Tkinter setup from CSE 493X lol
        self.window = tkinter.Tk()

        # App Grid layout. Coordinates are (row, col)
        # Text for Input Board
        # Input Frame (0, 0), Output Frame (0, 1)
        # Submit button (1, 0)

        # Input frame and output frame:
        # Title (0,0)
        # Board (1, 0)
        # Description (2, 0)

        # ==== SETUP INPUT FRAME ====
        self.input_frame = ttk.Frame(self.window)
        self.input_frame.grid(row=0, column=0)

        tkinter.Label(self.input_frame, text="Input").grid(row=0, column=0)
        # Make board canvas. Set width and height to be required width/height for number of cells
        # plus a bit extra.
        self.input_board_canvas = tkinter.Canvas(
            self.input_frame, width=(SIZE + 1) * CELL_SIZE, height=(SIZE + 1) * CELL_SIZE)
        self.input_board_canvas.grid(row=1, column=0, padx=10, pady=10)
        tkinter.Label(self.input_frame, text=INPUT_DESCRIPTION,
                      wraplength=250, justify="left").grid(row=2, column=0, padx=10)

        # ==== SETUP OUTPUT FRAME ====
        self.output_frame = ttk.Frame(self.window)
        self.output_frame.grid(row=0, column=1)

        # Label
        tkinter.Label(self.output_frame, text="Output").grid(row=0, column=0)

        # Setup output board (for viewing results).
        self.output_board_canvas = tkinter.Canvas(
            self.output_frame, width=(SIZE + 1) * CELL_SIZE, height=(SIZE + 1) * CELL_SIZE)
        self.output_board_canvas.grid(column=0, row=1, padx=10, pady=10)

        # Description
        tkinter.Label(self.output_frame, text=OUTPUT_DESCRIPTION,
                      wraplength=250, justify="left").grid(row=2, column=0, padx=10)

        # ==== Setup Internal State Logic ====
        # Create internal board representation, have it take ownership of canvas (will handle drawing and
        # updating based on input).
        self.input_board: Board = Board(
            self.input_board_canvas, SIZE, bind_callbacks=True)

        self.output_board: Board = Board(
            self.output_board_canvas, SIZE, bind_callbacks=False)

        # ==== Add Button ====
        self.submit_button = ttk.Button(
            self.window, text="Get a valid predecessor!", command=self.submit_query)
        self.submit_button.grid(row=1, column=0)

    def constrain(self, solver: z3.Solver, slice: golz3.Slice):
        """
        Add constraints to require that the provided slice matches the current board state.

        Args:
            solver (Solver): The Z3 Solver to add constraints to.
            vars (Slice): Set of variables representing cell states over time.
        """

        for row in range(0, SIZE):
            for col in range(0, SIZE):
                if self.input_board.get_cell_state(row, col):
                    solver.add(slice[row][col] == 1)
                else:
                    # Must remember to constrain in the negative case too
                    solver.add(slice[row][col] == 0)

    def submit_query(self):
        solver = z3.Solver()
        state: list[golz3.Slice] = golz3.make_life(
            solver=solver, grid_size=SIZE, time_steps=2)

        # Constrain post state to match selected pattern.
        self.constrain(solver, state[-1])

        # Run the query
        # print(solver.sexpr())
        query_result = solver.check()
        print(f"Query result: {query_result}")

        # Print the model
        model = solver.model()
        golz3.print_model(model, state)

        # Also visualize the first time step of model in output grid.
        result = golz3.model_to_python(model, state)
        self.output_board.set_board_state(result[0])
        # Redraw board with updated state.
        self.output_board.draw()

if __name__ == '__main__':
    App()
    # Kick off tkinter
    tkinter.mainloop()
