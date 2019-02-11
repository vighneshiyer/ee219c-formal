package formal

import utest._

object SATTest extends TestSuite {
  val tests = Tests {
    'bruteForce - {
      'lectureExample - {
        // Recreate the CNF formula on the SAT lecture (slide 6)
        val cnf: CNFFormula = Set(
          Set( 1,  2,  3),
          Set(-1, -2,  3),
          Set( 1, -2, -3),
          Set(-1,  2, -3)
        )
        val result = BruteForceSAT.solve(cnf)
        assert(result._1)
        println(result._2)
      }
      'complexExample - {

      }
      'unsatExample - {

      }
    }
  }
}
