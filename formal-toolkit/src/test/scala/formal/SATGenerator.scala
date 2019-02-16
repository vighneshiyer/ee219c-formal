package formal

import scala.util.Random.{nextInt, nextBoolean}

object SATGenerator {
  /**
    * Generate a random set of integers in the range 1 - n (inclusive)
    * @param n Upper bound on range of integers
    * @param k Number of elements in random set
    * @return Random set
    */
  def randomSet(n: Int, k: Int): Set[Int] = {
    val s = collection.mutable.Set.empty[Int]
    while (s.size < k) {
      s.add(1 + nextInt(n))
    }
    s.toSet
  }

  /**
    * Generate a k-SAT problem with n variables and m clauses.
    * @param n Number of variables
    * @param m Number of clauses
    * @param k Number of literals per clause
    * @return A randomly generated CNF formula
    */
  def generate(n: Int, m: Int, k: Int): CNFFormula = {
    val clauses = Seq.fill(m) {
      val literals = randomSet(n, k).map {
        v => if (nextBoolean()) v else v * -1
      }
      literals
    }
    clauses.toSet
  }
}
