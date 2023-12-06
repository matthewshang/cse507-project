import tkinter
import math

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


class Board:
    """
    The Game of Life board.
    """

    def __init__(self,
                 canvas: tkinter.Canvas,
                 size: int,
                 board_offset: int = 10,
                 bind_callbacks=True):
        """Create a new Game of Life Board.

        Args:
            canvas (Canvas): Canvas to use for drawing life board. This Board object
                takes ownership of the Board and will clear/draw to it.
            size (int): side length of grid in terms of number of cells.
            board_offset (int): offset from top and left side of canvas to draw board.
            bind_callbacks (bool): if true, then bind callbacks for this Board (so it
                can be interacted with by clicking).
        """
        self.canvas = canvas
        self.size: int = size
        self.board_offset = board_offset
        # 2D array of Cell objects representing the state of the board.
        self.init_board()

        if bind_callbacks:
            self.bind_callbacks()

        canvas.delete("all")
        self.draw()

    def init_board(self):
        """
        Initialize the board to be empty.
        """
        self.board = [[Cell(0) for col in range(self.size)]
                      for row in range(self.size)]

    def set_board_size(self, size: int):
        """
        Set the size of the board to the given size. This will clear the board.

        Args:
            size (int): new size of board.
        """
        self.size = size
        self.init_board()

    def cell_size(self) -> float:
        """
        Return the size of each cell in the canvas.
        """
        return (self.canvas.winfo_reqwidth() - 2 * self.board_offset) / self.size

    def draw(self) -> None:
        """
        Draw the board. Clears previous state of canvas.
        """
        self.canvas.delete("all")
        # Loop over and draw a square for each
        cell_size = self.cell_size()
        for row in range(self.size):
            for col in range(self.size):
                # Mysterious OFFSETs are to get grid lines to all draw (otherwise top and left side
                # of grid are cut off)
                fill = "gray26" if self.board[row][col].state else "white"
                self.canvas.create_rectangle(
                    self.board_offset + col * cell_size,
                    self.board_offset + row * cell_size,
                    self.board_offset + (col + 1) * cell_size,
                    self.board_offset + (row + 1) * cell_size,
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
        cell_size = self.cell_size()
        row = math.floor((y - self.board_offset) / cell_size)
        col = math.floor((x - self.board_offset) / cell_size)
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
                f"Row {row} and column {col} not within grid (grid size={self.size})"
            )

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
                f"Row {row} and column {col} not within grid (grid size={self.size})"
            )

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
                    f"All rows of `state` must have {self.size} rows. Row {row} of state is of length: {len(state[row])}"
                )
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
