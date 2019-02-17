package formal

import utest._
import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets

import scala.concurrent._
import sys.process._
import scala.concurrent.ExecutionContext.Implicits.global

object PigeonHoleTest extends TestSuite {
  val tests = Tests {
    'pigeon - {
      val durations = (4 to 15).map {
        n =>
          val cnf = PigeonHoleProblem.problem(n)
          val dimacs = DIMACS.toDIMACS(cnf)
          Files.write(Paths.get("pigeon_hole.cnf"), dimacs.getBytes(StandardCharsets.UTF_8))
          val t1 = System.nanoTime
          val p = "minisat pigeon_hole.cnf".run() // start asynchronously
          val f = Future(blocking(p.exitValue())) // wrap in Future
          try {
            Await.result(f, duration.Duration(60, "sec"))
          } catch {
            case _: TimeoutException =>
              println("TIMEOUT!")
              p.destroy()
              p.exitValue()
          }
          (System.nanoTime - t1) / 1e9d
      }
      Files.write(Paths.get("pigeon_hole.results"), durations.toString.getBytes(StandardCharsets.UTF_8))
    }
  }
}
