import Mathlib

namespace MathlibPlus.Algebra.Claim8596

/-- Exact displayed boundary-stagger/energy statement.  The packet omits the
index domain, so indices are made explicit as integers. -/
theorem boundaryStaggerEnergy_claim8596 (a : ℤ → ℝ) (k : ℤ) :
    let U_k := a (2 * k - 1) ^ 2 - a (2 * k - 2) ^ 2
    let E_k :=
      (a (2 * k - 1) - a (2 * k - 2)) ^ 2 +
        (a (2 * k) - a (2 * k + 1)) ^ 2
    E_k ≥ 0 := by
  dsimp
  positivity

end MathlibPlus.Algebra.Claim8596
