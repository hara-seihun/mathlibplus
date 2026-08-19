import Mathlib

namespace MathlibPlus.NumberTheory

/-- Claim 10546: the standard multiplication-by-`m` carry transducer has
uniform `q` transition counts whenever the base is `b = m * q`. -/
def divisibleBaseTransitionCount : Prop :=
  ∀ (m q b c k : ℕ),
    2 ≤ m →
    1 ≤ q →
    b = m * q →
    c < m →
    k < m →
    ((Finset.range b).filter
      (fun d : ℕ => (m * d + c) / b = k)).card = q ∧
      q = b / m

end MathlibPlus.NumberTheory
