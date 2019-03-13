#! /usr/bin/python2.7
import z3

from sumsudoku import *

# ----------------------------------------
# Part (c): Unique solutions to Sum-Sudoku
# ----------------------------------------

def lock_cells(S, flags, g, grid_vals, bypass=False):
    assert len(flags) == len(g[3]) == len(grid_vals)
    fixed_cells = filter(lambda x: x[2], zip(g[3], grid_vals, flags))
    S.add(reduce(lambda a, b: z3.And(a, b), map(lambda x: x[0] == x[1], fixed_cells), True))
    if not bypass:
        avoid_prev_assn = filter(lambda x: not x[2], zip(g[3], grid_vals, flags))
        S.add(reduce(lambda a, b: z3.Or(a, b), map(lambda x: x[0] != x[1], avoid_prev_assn), False))

def make_puzzle_unique(initial_grid):
    (row_vals, col_vals, grid_vals) = initial_grid
    g1 = list(gridvars(('r', 'c', 'x1'), n, m))

    S = z3.Solver()
    S.add(valid(g1))
    # Enforce equal row and column sums to the initial_grid
    S.add(reduce(lambda a, b: z3.And(a, b), map(lambda x: x[0] == x[1], zip(g1[0], row_vals))))
    S.add(reduce(lambda a, b: z3.And(a, b), map(lambda x: x[0] == x[1], zip(g1[1], col_vals))))
    valid_flags = []
    for removals in range(9):
        for i in itertools.combinations(range(n*n), removals):
            # i represents cells which are 'empty'
            flags = [False if x in i else True for x in range(n*n)]
            S.push()
            lock_cells(S, flags, g1, grid_vals)
            r = S.check()
            # if there's no model, then there still exists a unique solution
            if r == z3.unsat:
                valid_flags.append(flags)
            S.pop()
            print(removals, i, r)
    flags = valid_flags[-1]
    print(flags)
    lock_cells(S, flags, g1, grid_vals, bypass=True)
# Your "result" should be stored in the variable flags. flags should be a
# boolean array of length n*n in row-major order. flags[n*i + j] = false iff 
# row i, column j of the puzzle is "empty."

# ---- DON'T CHANGE THE CODE BELOW -------
    r = S.check()
    if r == z3.sat:
        pretty_print(extract_model(S.model(), g1), flags)
    else:
        assert False

if __name__ == '__main__':
    init_puzzle = solve_sum_sudoku()
    make_puzzle_unique(init_puzzle)
    
