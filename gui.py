"""
GUI application for submitting Game of Life queries 
"""

import tkinter
from tkinter import ttk
import itertools
from z3 import *

# Side length in px of cells when drawn to board.
CELL_SIZE = 30

class Cell:
    """
    A single cell in the Game of Life board.
    """
    def __init__(self, alive=0):
        self.alive = alive

# Board offset from top and left side of canvas so that lines draw.
BOARD_OFFSET = 10

class Board:
    """
    The Game of Life board.
    """
    def __init__(self, canvas: tkinter.Canvas, size: int):
        """Create a new Game of Life Board.

        Args:
            canvas (Canvas): Canvas to use for drawing life board. This Board object
                takes ownership of the Board and will clear/draw to it.
            size (int): side length of grid in terms of number of cells.
        """
        self.canvas = canvas
        self.size: int = size
        # 2D array of Cell objects representing the state of the board.
        self.board: list[list[Cell]] = [[Cell(0) for col in range(size)] for row in range(size)]

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
                fill = "gray26" if self.board[row][col].alive else "white"
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
    
    def on_left_click(self, event):
        # print(f"Click at x: {event.x}, y: {event.y}", end="")

        # row, col = self.coord_to_row_col(event.x, event.y)
        # print(f" row={row}, col={col}")

        cell = self.coord_to_cell(event.x, event.y)

        if not cell:
            return

        # Flip cell from dead to alive.
        cell.alive = 0 if cell.alive else 1
        
        self.draw()


WIDTH = 800
HEIGHT = 600
SIZE = 3


class App:
    """
    Top level application
    """
    def __init__(self):
        # (tenzin): Copying a good part of the Tkinter setup from CSE 493X lol
        self.window = tkinter.Tk()
        self.board_canvas = tkinter.Canvas(
            self.window, width=WIDTH, height=HEIGHT)
        self.board_canvas.grid(column=0, row=0, padx=10, pady=10)

        # Create internal board representation, have it take ownership of canvas.
        self.board = Board(self.board_canvas, SIZE)

        # Store the Solver instance which will actually do the work
        self.solver = Solver()


if __name__ == '__main__':
    App()
    # Kick off tkinter
    tkinter.mainloop()
