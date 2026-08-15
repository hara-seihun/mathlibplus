import Mathlib

namespace MathlibPlus.Open

/--
The transferred Volterra weight has the displayed fourth-order action, with a
coefficient of the sinh term that changes sign as the spectral parameter varies.
-/
def transferredVolterraWeightSignChangingTerm : Prop :=
  let w : ℝ → ℝ → ℝ := fun ω u => u * Real.cosh (ω * u)
  let P : ℝ → ℝ → ℝ :=
    fun x z => ((z + (1 : ℝ) / 2) ^ 2 + x ^ 2) *
      ((z - (1 : ℝ) / 2) ^ 2 + x ^ 2)
  let L : ℝ → (ℝ → ℝ) → ℝ → ℝ :=
    fun x f u =>
      iteratedDeriv 4 f u +
        (2 * x ^ 2 - (1 : ℝ) / 2) * iteratedDeriv 2 f u +
        (x ^ 2 + (1 : ℝ) / 4) ^ 2 * f u
  (∀ x ω : ℝ,
      deriv (P x) ω = 4 * ω * (ω ^ 2 + x ^ 2 - (1 : ℝ) / 4) ∧
        ∀ u : ℝ,
          L x (w ω) u =
            P x ω * u * Real.cosh (ω * u) +
              (4 * ω * (ω ^ 2 + x ^ 2 - (1 : ℝ) / 4)) *
                Real.sinh (ω * u)) ∧
    ∀ x : ℝ,
      ∃ omegaPos omegaNeg : ℝ,
        0 < 4 * omegaPos * (omegaPos ^ 2 + x ^ 2 - (1 : ℝ) / 4) ∧
          4 * omegaNeg * (omegaNeg ^ 2 + x ^ 2 - (1 : ℝ) / 4) < 0

end MathlibPlus.Open
