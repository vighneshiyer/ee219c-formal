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
    // TODO: change this to shuffle the sequence (1 to n) and take k elements
    // See this SO answer: https://stackoverflow.com/questions/32932229/how-to-randomly-sample-from-a-scala-list-or-array
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
      // TODO: bug, if multiple random clauses are identical, they get collapsed in the set
      val literals = randomSet(n, k).map {
        v => if (nextBoolean()) v else v * -1
      }
      literals
    }
    clauses.toSet
  }
}
