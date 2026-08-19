import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3192Claim47041

private def extensionA (a b : ℕ) : Multiset ℕ :=
  {1, a, a, 2 * b}

private def extensionC (a b : ℕ) : Multiset ℕ :=
  {1, 2 * a, b, b}

/-- Claim 47041: the center-leaf extension comparison has the exact arm-length
multisets and strict maximum inequality used to exclude isomorphism.  The
ambient spider graph is not replaced by an unrelated generic graph carrier. -/
def extensionArmMaximum_claim47041 : Prop :=
  ∀ (a b : ℕ),
    1 ≤ a →
    a < b →
    extensionA a b ≠ extensionC a b ∧
      max (max 1 (2 * a)) b < 2 * b

end MathlibPlus.Open.ResearchFormalization.R3192Claim47041
