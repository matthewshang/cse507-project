"""
GUI application for submitting Game of Life queries 
"""

import tkinter
from tkinter import ttk


class Board:
    """
    The Game of Life board.
    """
    def __init__(self, size: int):
        """Create a new Game of Life Board.

        Args:
            size (int): side length of grid.
        """
        self.size = size
        # Default initialize board to all empty
        self.board = [[0 for col in range(size)] for row in range(size)]
        pass
    
    def draw(self, frame: tkinter.Frame) -> None:
        """
        Draw the board.
        """
        # Loop over and draw a square for each 
        for row in range(self.size):
            for col in range(self.size):
                tkinter.Button(frame, text="Bleh", width=5, height=2).grid(row=row, column=col)


WIDTH = 800
HEIGHT = 600
SIZE = 3

class App:
    """
    Top level application
    """
    def __init__(self):
        self.board = Board(SIZE)
        # (tenzin): Copying a good part of the Tkinter setup from CSE 493X lol
        self.window = tkinter.Tk()
        self.frame = ttk.Frame(self.window, padding=10)
        self.frame.grid(column=0, row=0)
        # ttk.Label(self.frame, text="Hello World!").grid(column=0, row=0)

        # Draw board
        self.board_frame = ttk.Frame(self.window, padding=10).grid(column=0, row=1)
        self.board.draw(self.board_frame)

if __name__ == '__main__':
    App()
    # Kick off tkinter
    tkinter.mainloop()
