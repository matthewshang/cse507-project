"""
GUI application for visualizing Game of Life simulations.
"""
import tkinter
from tkinter import ttk

WIDTH = 800
HEIGHT = 800
SIZE = 6

class App:
    """
    Top level application
    """

    def __init__(self):
        self.window = tkinter.Tk()

        self.canvas = tkinter.Canvas(self.window, width=WIDTH, height=HEIGHT)
        self.canvas.grid(row=0, column=0, padx=10, pady=10)

        self.time_slider = tkinter.Scale(self.window, from_=0, to=10, orient='horizontal')
        self.time_slider.grid(row=1, column=0, padx=10)

if __name__ == "__main__":
    App()
    tkinter.mainloop()