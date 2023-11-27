# {ProjectName}

## Intro

{ProjectName} investigates applying solvers to the classic recreational math game/puzzle/cellular-automata: Conway's Game of Life.

## Setup

At a high-level these are the required steps:
1. Clone this repo
2. Install z3-solver pypi package

Unfortunately the `z3-solver` package ([LINK](https://pypi.org/project/z3-solver/)) isn't available as a conda package, so you'll have to use `pip` to install the package. (We looked into this but it's a bit of a pain to setup as a proper package, can probably be done though by setting up recipe to install from z3-solver wheel file).
