import Mathlib

namespace MathlibPlus.Algebra.ElementaryArithmeticClaims

/-- Claim 30783: the exact solutions of the orbit-count equation in the two
specified prime cases. -/
def orbit_count_solutions_claim30783 : Prop :=
  ∀ (a b p : ℕ),
    a * p + b = 12 →
      (p = 7 → ((a = 0 ∧ b = 12) ∨ (a = 1 ∧ b = 5))) ∧
        (p = 11 → ((a = 0 ∧ b = 12) ∨ (a = 1 ∧ b = 1)))

end MathlibPlus.Algebra.ElementaryArithmeticClaims
