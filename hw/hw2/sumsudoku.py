import z3
from math import ceil, log
import itertools
from functools import reduce
import typing
from typing import List
import numpy as np

# Parameters for Sum-Sudoku
n = 3
m = 5

def flatten(grid):
    return [item for sublist in grid for item in sublist]

# This function creates the variables.
def gridvars(names, n, m):
    rowsums = [var('%s%d' % (names[0], i)) for i in range(n)]
    colsums = [var('%s%d' % (names[1], i)) for i in range(n)]
    grid = [[var('%s_%d_%d' % (names[2], i, j)) for j in range(n)] for i in range(n)]

    return (rowsums, colsums, grid, flatten(grid))

# ----------------------------------------
# Part (a): Valid solutions to Sum-Sudoku
# ------ IMPLEMENT YOUR CODE HERE --------
def transpose(l: List[List]) -> List[List]:
    return [list(i) for i in zip(*l)]

def var(name):
    "Create a variable of the appropriate type here."
    return z3.Int(name)

def val(v):
    """Create an SMT literal of the appropriate type that corresponds to the
    Python integer 'v' here."""
    return z3.IntVal(v)

def valid(g):
    """Given the variables 'g' create a formula that encodes validity of the
    sum-sudoku instance for these variables."""
    #g[2] = np.reshape(g[3], (n, n))
    # Ensure all rows and all columns have unique values
    def unique_across_rows():
        for row in g[2]:
            for combo in itertools.combinations(row, 2):
                yield combo[0] != combo[1]
    rows_unique = reduce(lambda a, b: z3.And(a, b), unique_across_rows())
    def unique_across_cols():
        for row in transpose(g[2]):
            for combo in itertools.combinations(row, 2):
                yield combo[0] != combo[1]
    cols_unique = reduce(lambda a, b: z3.And(a, b), unique_across_cols())
    # Ensure all values are between 1 and m
    def values_in_range():
        for row in g[2]:
            for elem in row:
                yield z3.And(elem >= 1, elem <= m)
    vals_range = reduce(lambda a, b: z3.And(a, b), values_in_range())
    # Relate the row and column sums to the grid
    def row_relation():
        for row_num in range(n):
            yield g[0][row_num] == reduce(lambda a, b: a + b, g[2][row_num])
    row_sum_rel = reduce(lambda a, b: z3.And(a, b), row_relation())
    def col_relation():
        for col_num in range(n):
            yield g[1][col_num] == reduce(lambda a, b: a + b, transpose(g[2])[col_num])
    col_sum_rel = reduce(lambda a, b: z3.And(a, b), col_relation())
    return z3.And(rows_unique, cols_unique, vals_range, row_sum_rel, col_sum_rel)

# ---- DON'T CHANGE THE CODE BELOW -------
def extract_model(m, g):
    rows = [m.eval(rsi).as_long() for rsi in g[0]]
    cols = [m.eval(csi).as_long() for csi in g[1]]
    grid = [[m.eval(gij).as_long() for gij in gi] for gi in g[2]]
    return (rows, cols, grid)

def pretty_print(g, flags=None):
    (rows, cols, grid) = g
    header = ' | '.join(['%3s' % ''] + ['%3d' % ci for ci in cols])
    separator = '-' * len(header)
    print (header)
    print (separator)
    def to_str(v, fi):
        return '%3d' % v if fi else '%3s' % '-'

    for i, gr in enumerate(grid):
        int_values = [rows[i]] + gr
        if flags:
            flags_plus = [True] + flags[i*n:(i+1)*n]
            zipped_values = zip(flags_plus, int_values)
            str_values = [to_str(vi, fi) for fi, vi in zipped_values]
        else:
            str_values = ['%3d' % v for v in int_values]

        row = ' | '.join(str_values)
        print (row)
    print (separator)

def solve_sum_sudoku():
    g = gridvars(('r', 'c', 'x'), n, m)
    print(g)
    rs, cs = g[0], g[1]

    S = z3.Solver()
    S.add(valid(g))
    S.add(z3.And(rs[0] == val(8),
                 rs[1] == val(10),
                 rs[2] == val(10)))
    S.add(z3.And(cs[0] == val(8),
                 cs[1] == val(8),
                 cs[2] == val(12)))
    """
    S.add(z3.And(rs[0] == val(5),
                 rs[1] == val(7),))
                 #rs[2] == val(10)))
    S.add(z3.And(cs[0] == val(7),
                 cs[1] == val(5),))
                 #cs[2] == val(7)))
    """
    if S.check() == z3.unsat:
        assert False

    count = 0
    while S.check() == z3.sat and count < 1:
        model = S.model()
        row_vals = [model.eval(rs_i) for rs_i in g[0]]
        col_vals = [model.eval(cs_i) for cs_i in g[1]]
        grid_vals = [model.eval(gs_i) for gs_i in g[3]]
        pretty_print(extract_model(model, g))
        S.add(z3.Or(
            *map(lambda x: x[0] != x[1], zip(g[3],grid_vals))
        )) # prevent next model from using the same assignment as a previous model
        count = count + 1
    return (row_vals, col_vals, grid_vals)

if __name__ == '__main__':
    solve_sum_sudoku()
