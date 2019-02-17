package formal

object DIMACS {
  def toDIMACS(f: CNFFormula): String = {
    val headerComment = "c A CNF formula\n"
    val numClauses = f.size
    // TODO: I'm doing this a lot, maybe it is time to make CNFFormula more than just a type alias
    // TODO: Need to have variables as part of the object
    val numVariables = f.map(_.max).max
    val header = s"p cnf $numVariables $numClauses\n"
    val clauses = f.map {
      c => c.map(_.toString).mkString(" ") ++ " 0"
    }.mkString("\n")
    headerComment ++ header ++ clauses
  }
}
