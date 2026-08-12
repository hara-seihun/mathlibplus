import Mathlib

namespace MathlibPlus.Combinatorics

/-!
Formalization of admitted claim 10537.  The source names the two partition
sums `Z_+` and `Z_-` but leaves their formulas implicit in the claim line;
the packet witness gives the explicit polynomials below.
-/

/-- The explicit complete-prefix-code witness has the claimed difference factorization. -/
theorem exactDifferenceFactorization_claim10537 :
    let Zminus : ℝ → ℝ := fun q => 4 * q ^ 2
    let Zplus : ℝ → ℝ := fun q => q + q ^ 2 + q ^ 3 + 2 * q ^ 4
    ∀ q : ℝ, Zplus q - Zminus q = q * (2 * q - 1) * (q ^ 2 + q - 1) := by
  dsimp
  intro q
  ring

end MathlibPlus.Combinatorics
