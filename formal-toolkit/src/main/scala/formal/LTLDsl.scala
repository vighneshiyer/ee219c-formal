//package formal

// TODO: this is disgusting, do it properly with a union type
/*
sealed trait LTLFormula
final case class AtomicProposition(v: Variable, state: Boolean) extends LTLFormula
object AtomicProposition {
  def apply(v: Variable): AtomicProposition = AtomicProposition(v, state = true)
}
final case class AtomicPropositionSet(aps: Set[AtomicProposition]) extends LTLFormula
object AtomicPropositionSet {
  def apply(aps: AtomicProposition*): AtomicPropositionSet = AtomicPropositionSet(Set(aps:_*))
}
final case class LTLOr(l1: LTLFormula, l2: LTLFormula) extends LTLFormula
final case class LTLNot(l: LTLFormula) extends LTLFormula

case class Trace(trace: Seq[Set[AtomicProposition]]) {
  def satisfies(ltl: LTLFormula): Boolean = {
    ltl match {
      case ltl: AtomicProposition =>
        trace.head.contains(ltl)
      case _ => ???
    }
  }
}
*/
