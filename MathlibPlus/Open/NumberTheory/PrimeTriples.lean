import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-!
# Fixed even-gap prime triples

The source says "fixed positive even `a < c`".  This formalization reads that
as both gaps being positive and even, and expresses infinitude by an unbounded
set of prime starting points.
-/

/-- Claim 16907: some two fixed positive even gaps occur in infinitely many
prime triples. -/
def fixedEvenPrimeTriple : Prop :=
  ∃ a c : ℕ,
    0 < a ∧ 0 < c ∧ Even a ∧ Even c ∧ a < c ∧
      ∀ B : ℕ, ∃ p : ℕ,
        B ≤ p ∧ Nat.Prime p ∧ Nat.Prime (p + a) ∧ Nat.Prime (p + a + c)

end MathlibPlus.Open.NumberTheory
