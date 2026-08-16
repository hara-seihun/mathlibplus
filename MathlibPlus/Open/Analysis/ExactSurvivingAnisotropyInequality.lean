import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/--
The exact surviving anisotropy inequality for the three square ports of the
centered sixth-order spline carrier.
-/
def exactSurvivingAnisotropyInequality (r σ t : ℝ) (_hr : 0 < r) : Prop :=
  let c : ℝ := 32 / 10395
  let g₆ : ℝ → ℝ := fun u =>
    (1 / 12 : ℝ) *
      Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp u))) (fun n =>
        ((n : ℝ) / Real.exp u) ^ 2 *
          (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 4)
  let β₆ : ℝ → ℝ := fun u => g₆ u - c * Real.exp u
  let h₆ : ℝ → ℝ := fun u => deriv β₆ u - β₆ u
  let I : (ℝ → ℝ) → ℂ := fun P =>
    ∫ u in Set.Ioi (0 : ℝ),
      (P u : ℂ) * Complex.exp (-((σ : ℂ) * (u : ℂ))) *
        (h₆ u : ℂ) * Complex.exp (Complex.I * ((t : ℂ) * (u : ℂ)))
  let S₀ : ℂ := I (fun u => u ^ 2)
  let S₁ : ℂ := I (fun u => u * (2 * r - u))
  let S₂ : ℂ := I (fun u => (u - 2 * r) ^ 2)
  ‖S₁‖ ^ 2 - ‖S₀‖ * ‖S₂‖ ≤
    (1 / 2 : ℝ) * (‖S₂‖ - ‖S₀‖) ^ 2

end
end MathlibPlus.Open.Analysis
