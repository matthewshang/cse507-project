# GOLZ3

## Intro

GOLZ3 investigates applying solvers to the classic recreational math game/puzzle/cellular-automata: Conway's Game of Life. Slides we used for presenting the project are located under `Slides\GOLZ3.pptx`

## Setup

At a high-level these are the required steps:
1. Clone this repo
2. Use `pip` to install the `z3-solver` pypi package into the Python environment of your choice.

Unfortunately the `z3-solver` package ([LINK](https://pypi.org/project/z3-solver/)) isn't available as a conda package, so you'll have to use `pip` to install the package. (We looked into this but it's a bit of a pain to setup as a proper package, can probably be done though by setting up recipe to install from z3-solver wheel file).

## Running stuff

This section explains how to run stuff.

### Predecessor Search

The predecessor search gui is implemented in `backward_gui.py`. Run it with `python backward_gui.py` (requires Python 3.10+). The GUI contains instructions on how to use it.

You can save the solution the solver finds using the save button. This solution can then be viewed in the "forward GUI".

### Replaying Predecessor Search Solutions

Run the forward GUI with:
```python
python foward_gui.py
```

Load any saved predecessor search results and see what the solution looks like!

### Jupyter Notebooks

We implemented proofs of concepts for various Game of Life queries in various Jupyter notebooks. Run these notebooks with whatever Python environment you setup with the `z3-solver` package and you'll be ready to go. Step through the cells to see them in action!

Here are some chief ones we wanted to highlight:
- `more_life.ipynb` contains a bulk of examples. Just load it up using your Python environment as the kernel and step through the cells to see examples of how glider search, Garden of Eden searching, and more(!) can be implemented through Z3Py's API.
- `synth.ipynb` contains a very basic sketch of how a query can be constructed such that the solver synthesizes a Cellular Automaton rule that explains a given concrete pre and post state.
- `pseudobool.ipynb` contains a repeat of many examples from `more_life`, except that the constraint generation function has been modified to generate constraints in terms of Z3's provided Pseudo-boolean equations for counting `Bool`'s. These turned out to be pretty slow unfortunately.
