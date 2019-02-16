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
        val result = BruteForceSATSolver.solve(cnf)
        assert(result._1)
      }
      'complexExample - {
        // From here: https://people.sc.fsu.edu/~jburkardt/data/cnf/quinn.cnf
        val cnf = Set(
          Set(1,  2),
          Set(-2, -4),
          Set(3,  4),
          Set(-4, -5),
          Set(5, -6),
          Set(6, -7),
          Set(6,  7),
          Set(7, -16),
          Set(8, -9),
          Set(-8, -14),
          Set(9, 10),
          Set(9, -10),
          Set(-10, -11),
          Set(10, 12),
          Set(11, 12),
          Set(13, 14),
          Set(14, -15),
          Set(15, 16)
        )
        val result = BruteForceSATSolver.solve(cnf)
        assert(result._1)
      }
      'trivialUnsatExample - {
        val cnf = Set(
          Set(-1),
          Set(1)
        )
        val result = BruteForceSATSolver.solve(cnf)
        assert(!result._1)
      }
      'simpleUnsatExample - {
        val cnf = Set(
          Set(1, 2, 3),
          Set(1, 2, -3),
          Set(1, -2, 3),
          Set(1, -2, -3),
          Set(-1, 2, 3),
          Set(-1, 2, -3),
          Set(-1, -2 , 3),
          Set(-1, -2, -3)
        )
        val result = BruteForceSATSolver.solve(cnf)
        assert(!result._1)
      }
    }
    'generator - {
      val cnf = SATGenerator.generate(5, 4, 3)
      println(cnf)
      val dimacs = DIMACS.toDIMACS(cnf)
      println(dimacs)
    }
  }
}
