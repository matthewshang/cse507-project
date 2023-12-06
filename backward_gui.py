"""
GUI application for submitting Game of Life queries 
"""

from gui_common import Board
import tkinter
import tkinter.filedialog
from tkinter import ttk
import z3
import golz3
from timeit import default_timer as timer
from trajectory import Trajectory

# Board offset from top and left side of canvas so that lines draw.
BOARD_OFFSET = 10

CANVAS_SIZE = 400

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
        # Query Result (1, 1)

        # Input frame and output frame:
        # Title (0,0)
        # Board (1, 0)
        # Description (2, 0)

        # ==== SETUP INPUT FRAME ====
        self.input_frame = ttk.Frame(self.window)
        self.input_frame.grid(row=0, column=0)

        tkinter.Label(self.input_frame, text="Input").grid(row=0,
                                                           column=0,
                                                           padx=10)
        # Make board canvas.
        self.input_board_canvas = tkinter.Canvas(self.input_frame,
                                                 width=CANVAS_SIZE,
                                                 height=CANVAS_SIZE)
        self.input_board_canvas.grid(row=1, column=0, padx=10, pady=10)

        tkinter.Label(self.input_frame,
                      text=INPUT_DESCRIPTION,
                      wraplength=250,
                      justify="left").grid(row=2, column=0, padx=10)

        option_frame = ttk.Frame(self.input_frame)
        option_frame.grid(row=1, column=1)
        tkinter.Label(option_frame, text="Board\nsize").grid(row=0, column=0)
        self.size = 20
        self.size_scale = tkinter.Scale(option_frame,
                                        from_=3,
                                        to=30,
                                        orient='vertical')
        self.size_scale.grid(row=1, column=0)
        self.size_scale.set(self.size)

        tkinter.Label(option_frame, text="Time\nsteps").grid(row=2, column=0)
        self.time_scale = tkinter.Scale(option_frame,
                                        from_=2,
                                        to=8,
                                        orient='vertical')
        self.time_scale.grid(row=3, column=0)
        self.time_scale.set(2)

        tkinter.Label(option_frame, text="Sparsity").grid(row=4, column=0)
        self.sparsity_scale = tkinter.Scale(option_frame,
                                            from_=1,
                                            to=100,
                                            orient='vertical')
        self.sparsity_scale.grid(row=5, column=0)
        self.sparsity_scale.set(50)

        reset_button = ttk.Button(option_frame,
                                  text="Reset",
                                  command=self.reset)
        reset_button.grid(row=6, column=0)

        # ==== SETUP OUTPUT FRAME ====
        self.output_frame = ttk.Frame(self.window)
        self.output_frame.grid(row=0, column=1)

        # Label
        tkinter.Label(self.output_frame, text="Output").grid(row=0,
                                                             column=0,
                                                             padx=10)

        # Setup output board (for viewing results).
        self.output_board_canvas = tkinter.Canvas(self.output_frame,
                                                  width=CANVAS_SIZE,
                                                  height=CANVAS_SIZE)
        self.output_board_canvas.grid(column=0, row=1, padx=10, pady=10)

        # Description
        tkinter.Label(self.output_frame,
                      text=OUTPUT_DESCRIPTION,
                      wraplength=250,
                      justify="left").grid(row=2, column=0, padx=10)

        # ==== Setup Internal State Logic ====
        # Create internal board representation, have it take ownership of canvas (will handle drawing and
        # updating based on input).
        self.input_board: Board = Board(self.input_board_canvas,
                                        self.size,
                                        bind_callbacks=True)

        self.output_board: Board = Board(self.output_board_canvas,
                                         self.size,
                                         bind_callbacks=False)

        # ==== Add Button ====
        self.submit_button = ttk.Button(self.window,
                                        text="Get a valid predecessor!",
                                        command=self.submit_query)
        self.submit_button.grid(row=1, column=0)

        # === Add Result Label ====
        result_frame = ttk.Frame(self.window)
        result_frame.grid(row=1, column=1)
        self.result_label = ttk.Label(result_frame,
                                      text="Query Outcome: <None yet>",
                                      wraplength=200)
        self.result_label.grid(row=0, column=0)
        self.result = None
        ttk.Button(result_frame, text="Save", command=self.save).grid(row=0, column=1)

    def constrain(self, solver: z3.Solver, slice: golz3.Slice):
        """
        Add constraints to require that the provided slice matches the current board state.

        Args:
            solver (Solver): The Z3 Solver to add constraints to.
            vars (Slice): Set of variables representing cell states over time.
        """

        for row in range(0, self.size):
            for col in range(0, self.size):
                if self.input_board.get_cell_state(row, col):
                    solver.add(slice[row][col] == 1)
                else:
                    # Must remember to constrain in the negative case too
                    solver.add(slice[row][col] == 0)

    def reset(self):
        """
        Reset the input board to a random state.
        """
        # Get the new size
        self.size = int(self.size_scale.get())
        self.input_board.set_board_size(self.size)
        self.output_board.set_board_size(self.size)
        self.input_board.draw()
        self.output_board.draw()
        self.result = None

    def save(self):
        if self.result is not None:
            location = tkinter.filedialog.asksaveasfilename()
            if location:
                Trajectory(self.result).save(location)

    def submit_query(self):
        solver = z3.Solver()
        time_steps = int(self.time_scale.get())
        state: list[golz3.Slice] = golz3.make_life(solver=solver,
                                                   grid_size=self.size,
                                                   time_steps=time_steps)

        # Constrain post state to match selected pattern.
        self.constrain(solver, state[-1])

        # Constrain sparsity.
        sparsity = int(self.sparsity_scale.get())
        if sparsity != 100:
            max_cells = int(sparsity / 100 * self.size * self.size)
            solver.add(
                sum([
                    state[0][i][j] for j in range(self.size)
                    for i in range(self.size)
                ]) <= max_cells)

        # Run the query
        # print(solver.sexpr())
        start = timer()
        query_result = solver.check()
        end = timer()
        query_time = end - start
        print(f"Query result: {query_result}")

        # Default to clearing everything in output on failed query.
        result = [[[0] * self.size for _ in range(self.size)]]

        # Print the model
        if query_result == z3.sat:
            model = solver.model()
            # golz3.print_model(model, state)

            # Also visualize the first time step of model in output grid.
            result = golz3.model_to_python(model, state)
            self.result = result
            self.result_label.configure(
                text=f"Query outcome: SAT ({query_time:.2f}s)")
        else:
            self.result_label.configure(
                text=f"Query outcome: UNSAT ({query_time:.2f}s)")

        self.output_board.set_board_state(result[0])
        # Redraw board with updated state.
        self.output_board.draw()


if __name__ == '__main__':
    App()
    # Kick off tkinter
    tkinter.mainloop()
