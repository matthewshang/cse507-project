import pickle

class Trajectory:
    """
    A trajectory is a list of states, where each state is a 2D grid of cells.
    """
    def __init__(self, states: list[list[list[int]]]) -> None:
        self.states = states
        self.time_steps = len(states)
        self.grid_size = len(states[0])

    @staticmethod
    def load(path: str) -> "Trajectory":
        with open(path, "rb") as f:
            return pickle.load(f)
    
    def save(self, path: str) -> None:
        with open(path, "wb") as f:
            pickle.dump(self, f)