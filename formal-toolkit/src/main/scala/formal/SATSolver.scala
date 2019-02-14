package formal

trait SATSolver {
  def solve(f: CNFFormula): (Boolean, Option[Seq[Literal]])
  def satisfied(f: CNFFormula, assn: Seq[Literal]): Boolean = {
    f.forall {
      clause => clause.exists {
        l => assn.contains(l)
      }
    }
  }
}

object BruteForceSAT extends SATSolver {
  // From https://stackoverflow.com/questions/27101500/scala-permutations-using-two-lists
  // Useful to enumerate all possible T/F combinations of variables
  def prod[T](lst: Seq[T], n: Int) = Seq.fill(n)(lst).flatten.combinations(n).flatMap(_.permutations)

  override def solve(f: CNFFormula): (Boolean, Option[Seq[Literal]]) = {
    val literals: Set[Literal] = f.foldLeft(Set[Literal]()) {
      case (set, clause) => set.union(clause)
    }
    assert(!literals.contains(0))
    val variables = literals.map(_.abs).toSeq

    val searchResult = prod(Seq(1, -1), variables.size).find {
      assignment =>
        satisfied(f, (variables zip assignment).map {
          case (v, a) => v*a
        })
    }
    searchResult match {
      case Some(assn) => (true, Some(assn))
      case None => (false, None)
    }
  }
}
