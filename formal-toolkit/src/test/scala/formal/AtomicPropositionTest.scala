package formal

import utest._

object AtomicPropositionTest extends TestSuite {
  val tests = Tests {
    /*
    "satisfies works on LTL formulas consisting of a single atomic proposition" - {
      val x = Variable("p")
      val y = Variable("q")
      val p = AtomicProposition(x)
      val q = AtomicProposition(y)
      val l = p // The LTL formula consisting of just a single atomic proposition
      val t1 = Trace(Seq(
        Set(p), Set(p, q), Set(q), Set(q)
      ))
      val t2 = Trace(Seq(
        Set(), Set(), Set(p, q), Set(p), Set(), Set()
      ))
      assert(t1.satisfies(l))
      assert(!t2.satisfies(l))
    }
    */
  }
}
