/**
  * Variables are just numbers (Ints) (a higher-level map from Ints to human-readable variable names can exist)
  * A positive literal (i.e. variable == true) is (variable number)
  * A negative literal (i.e. variable == false) is -(variable number)
  * A CNF clause is a OR of literals e.g. (-1 + 2 + -3 + -4)
  * A CNF formula is an AND of CNF clauses e.g. (1 + 2 + 3)(-1 + -2 + 3)(1 + -2 + -3)
  */
package object formal {
  type Literal = Int
  type CNFClause = Set[Literal]
  type CNFFormula = Set[CNFClause]
}
