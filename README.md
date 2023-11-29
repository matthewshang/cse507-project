# {ProjectName}

## Intro

{ProjectName} investigates applying solvers to the classic recreational math game/puzzle/cellular-automata: Conway's Game of Life.

## Setup

At a high-level these are the required steps:
1. Clone this repo
2. Install z3-solver pypi package

Unfortunately the `z3-solver` package ([LINK](https://pypi.org/project/z3-solver/)) isn't available as a conda package, so you'll have to use `pip` to install the package. (We looked into this but it's a bit of a pain to setup as a proper package, can probably be done though by setting up recipe to install from z3-solver wheel file).

### Virtualenv

(Not necessary if you've already installed `z3-solver` python package, but if you want to keep in isolated from your main install, can follow these steps).

Install virtualenv: https://virtualenv.pypa.io/en/latest/installation.html

Create a new virtualenv for this repo (can just run command in root of repo):
```
virtualenv 507
```

Then activate environment... (use these commands whenever you want to activate environment).

Mac/Linux:
```
source <env_name>/bin/activate
```

Windows:
```
.\<env_name>\Scripts\activate
```

Install packages into environment (only need to do this when first setting up or when requirements.txt has been updated):
```
pip install -r requirements.txt
```
