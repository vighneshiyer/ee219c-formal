package formal

object DIMACS {
  def toDIMACS(f: CNFFormula): String = {
    val headerComment = "c A CNF formula\n"
    val numClauses = f.size
    // TODO: I'm doing this a lot, maybe it is time to make CNFFormula more than just a type alias
    val numVariables = f.foldLeft(Set.empty[Int]){
      case (s, c) => s.union(c.map(_.abs))
    }.size
    val header = s"p cnf $numVariables $numClauses\n"
    val clauses = f.map {
      c => c.map(_.toString).mkString(" ")
    }.mkString("\n")
    headerComment ++ header ++ clauses
  }
}
