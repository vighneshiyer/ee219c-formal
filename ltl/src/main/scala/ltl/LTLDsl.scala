package ltl

case class Variable(name: String)
// TODO: this is disgusting, do it properly with a union type
trait LTLFormula
case class AtomicProposition(v: Variable, state: Boolean) extends LTLFormula
case class AtomicPropositionSet(aps: Set[AtomicProposition]) extends LTLFormula {
  def apply(aps: AtomicProposition*): AtomicPropositionSet = AtomicPropositionSet(Set(aps:_*))
}
case class LTLOr(l1: LTLFormula, l2: LTLFormula) extends LTLFormula
case class LTLNot(l: LTLFormula) extends LTLFormula

// TODO: refactor into type alias
case class Trace(vals: Seq[Set[AtomicProposition]])

object Checker {
  def satisfies(trace: Trace, ltl: LTLFormula): Boolean = {
    ltl match {
      case ltl: AtomicProposition =>
        trace.vals.head.contains(ltl)
    }
  }
}
