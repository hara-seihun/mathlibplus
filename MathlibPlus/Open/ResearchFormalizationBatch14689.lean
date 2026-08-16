import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch14689

noncomputable section

/-- Claim 14689: the tail integral and its positive Epstein-lattice slice bound. -/
def claim14689 : Prop :=
  (∀ A : ℝ, 0 < A →
    (∫ x in Set.Ioi (0 : ℝ),
        Real.rpow (x ^ 2 + A ^ 2) (-3 / 2 : ℝ)) = (A ^ 2)⁻¹) ∧
  (∀ n : ℤ, 0 < n →
    (∑' m : ℤ,
      Real.rpow ((m : ℝ) ^ 2 + 5 * (n : ℝ) ^ 2) (-3 / 2 : ℝ)) ≤
      (5 * Real.sqrt 5 * (n : ℝ) ^ 3)⁻¹ +
        2 * (5 * (n : ℝ) ^ 2)⁻¹)

end

end MathlibPlus.Open.ResearchFormalizationBatch14689
