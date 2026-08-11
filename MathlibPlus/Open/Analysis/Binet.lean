import Mathlib

/-!
# First-correction Binet residual

Registry statement for admitted claim 212 from packet `C-0014`.
-/

namespace MathlibPlus.Open.Analysis.Binet

/-- After extracting the first Binet correction, the first eight derivatives of the
residual kernel obey the displayed uniform bound, and the accompanying Bose integral
has value `1/240`. The variables are restricted to the positive Binet domain: `t > 0`
and `u ≥ 0`. -/
def firstCorrectionResidual : Prop :=
  (∀ k : ℕ, k ≤ 7 → ∀ t u : ℝ, 0 < t → 0 ≤ u →
    |iteratedDeriv k (fun s : ℝ => s ^ (-2 : ℤ) / (s ^ 2 + u ^ 2)) t| ≤
      ((k.factorial * Nat.choose (k + 3) 3 : ℕ) : ℝ) / t ^ (k + 4)) ∧
  (∫ u : ℝ in Set.Ioi 0, u ^ 3 / (Real.exp (2 * Real.pi * u) - 1)) =
    (1 : ℝ) / 240

end MathlibPlus.Open.Analysis.Binet
