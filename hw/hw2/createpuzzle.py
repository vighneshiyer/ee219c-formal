import z3

from sumsudoku import *

# ----------------------------------------
# Part (b): Unique solutions to Sum-Sudoku
# ----------------------------------------
def create_puzzle():
    g1 = list(gridvars(('r', 'c', 'x'), n, m))
    rs, cs, xv = g1[0], g1[1], g1[3]
    S = z3.Solver()
    S.add(
        z3.Exists([*rs, *cs],
            z3.ForAll([*xv],
                z3.Or(
                    z3.And(rs == rs, cs == cs, valid([rs, cs, None, xv])),
                    z3.And(rs != rs, cs != cs, z3.Not(valid([rs, cs, None, xv])))
                )
            )
        )
    )
    #S.add(valid(g1))
    def do_assn():
        assignments = itertools.product(*[range(1, m+1) for r in range(2*n)])
        for a in assignments:
            v = z3.Bool('%s' % a.__str__())
            S.add(z3.Implies(v == True, reduce(lambda a, b: z3.And(a, b), map(lambda x: x[0] == x[1], zip(a, g1[3])))))
            S.add(z3.Implies(reduce(lambda a, b: z3.Or(a, b), map(lambda x: x[0] != x[1], zip(a, g1[3]))), v == False))
            #S.add(z3.Implies(reduce(lambda a, b: z3.And(a, b), map(lambda x: x[0] == x[1], zip(a, g1[3]))), v == True))
            yield v
    #assn_vars = [x for x in do_assn()]
    #S.add(z3.PbEq([(x,1) for x in assn_vars], 1))
    #S.add(z3.Exists([*g1[0], *g1[1]], z3.ForAll([*g1[3]],
        #z3.PbEq([(valid(g1), 1)], 1))))
    """
    def one_hot():
        for cell in g1[3]:
            exact_eq = [z3.Bool('%s_%d'% (cell, i)) for i in range(1, m+1)]
            print(exact_eq)
            for e in range(1, m+1):
                S.add(z3.Implies(cell == val(e), exact_eq[e-1] == True))
                S.add(z3.Implies(cell != val(e), exact_eq[e-1] == False))
            yield z3.PbEq([(x,1) for x in exact_eq], 1)
    S.add(reduce(lambda a, b: z3.And(a, b), one_hot()))
    """
# ---- DON'T CHANGE THE CODE BELOW -------
    count = 0
    if S.check() == z3.unsat:
        print("UNSAT")
        return
    while S.check() == z3.sat and count < 1:
        model = S.model()
        pretty_print(extract_model(S.model(), g1))
        row_vals = [model.eval(rs_i) for rs_i in g1[0]]
        col_vals = [model.eval(cs_i) for cs_i in g1[1]]
        S.add(z3.Or(
            *map(lambda x: x[0] != x[1], zip(g1[0],row_vals))
        )) # prevent next model from using the same assignment as a previous model
        S.add(z3.Or(
            *map(lambda x: x[0] != x[1], zip(g1[1],col_vals))
        )) # prevent next model from using the same assignment as a previous model
        count = count + 1

if __name__ == '__main__':
    create_puzzle()
