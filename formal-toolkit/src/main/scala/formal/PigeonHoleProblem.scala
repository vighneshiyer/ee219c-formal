package formal

object PigeonHoleProblem {
  /**
    * Generate the CNF formula of the pigeon-hole problem for n pigeons.
    *
    * x_ij = pigeon i placed in hole j
    * 1) All pigeons placed in at least one hole
    *   OR (across j's) x_ij, for all pigeons
    * 2) No two pigeons can be placed in the same hole
    *   not (x_ik) OR not (x_ij), for all holes, for all pairs of pigeons
    * @param n The number of pigeons
    * @return The CNF formula encoding this pigeon-hole problem
    */
  def problem(n: Int): CNFFormula = {
    val pigeons = 1 to n
    val holes = 1 until n
    // stride on pigeons with stride size of holes
    def pigeonHoleToVariable(p: Int, h: Int): Int = {
      (p-1)*holes.size + h
    }
    val everyPigeonInOneHole: CNFFormula = pigeons.map {
      p => holes.foldLeft(Set.empty[Int]) {
        case (s, h) => s.union(Set(pigeonHoleToVariable(p, h)))
      }
    }.toSet
    val noTwoPigeonsPerHole = holes.foldLeft(Set.empty[Set[Int]]) {
      case (ss, h) => ss.union(pigeons.combinations(2).foldLeft(Seq.empty[Set[Int]]) {
        case (s, p) => s :+ Set(-pigeonHoleToVariable(p(0), h), -pigeonHoleToVariable(p(1), h))
      }.toSet)
    }
    everyPigeonInOneHole.union(noTwoPigeonsPerHole)
  }
}
