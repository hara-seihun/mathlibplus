import Mathlib

namespace MathlibPlus.Open.Algebra.Claim37803

open scoped BigOperators

/-- Claim 37803: a common context factor annihilates every two-row
projective minor. -/
def claim37803 : Prop :=
  ∀ (H_A H_B : Polynomial ℚ) (L : ℕ → Polynomial ℚ)
    (u v : ℕ),
    (H_A * L u) * (H_B * L v) -
        (H_B * L u) * (H_A * L v) = 0

end MathlibPlus.Open.Algebra.Claim37803
