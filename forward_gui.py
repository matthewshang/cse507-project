"""
GUI application for visualizing Game of Life simulations.
"""
import tkinter
import tkinter.filedialog
from tkinter import ttk
from gui_common import Board
from frames import Frames

WIDTH = 400
HEIGHT = 400
SIZE = 6

class App:
    """
    Top level application
    """

    def __init__(self):
        self.window = tkinter.Tk()

        canvas = tkinter.Canvas(self.window, width=WIDTH, height=HEIGHT)
        canvas.grid(row=0, column=0, padx=10, pady=10)
        self.board = Board(canvas, SIZE, bind_callbacks=False)

        button_frame = ttk.Frame(self.window)
        button_frame.grid(row=1, column=0, padx=10, pady=10)
        tkinter.Button(button_frame, text="Load", command=self.load).grid(row=0, column=0, padx=10)
        tkinter.Button(button_frame, text="Step", command=self.step).grid(row=0, column=1, padx=10)
        tkinter.Button(button_frame, text="Play/Pause", command=self.toggle).grid(row=0, column=2, padx=10)

        self.frames = None
        self.playing = False
        self.frame_index = 0

    def load(self):
        location = tkinter.filedialog.askopenfilename()
        if location:
            self.frames = Frames.load(location)
            self.playing = False
            self.frame_index = 0
            self.board.set_board_size(self.frames.grid_size)
            self.step()

    def step(self):
        if self.frames is None:
            return

        self.board.draw()
        self.frame_index = (self.frame_index + 1) % self.frames.time_steps
        self.board.set_board_state(self.frames.states[self.frame_index])
        if self.playing:
            self.window.after(500, self.step)

    def toggle(self):
        self.playing = not self.playing
        if self.playing:
            self.step()

if __name__ == "__main__":
    App()
    tkinter.mainloop()