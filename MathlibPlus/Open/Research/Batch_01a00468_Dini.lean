import Mathlib

namespace MathlibPlus.Open.Research.Batch_01a00468_Dini

noncomputable section

open scoped ComplexConjugate

def diniTerm (L : ℝ) (z : ℂ) : ℂ :=
  z * Complex.sin ((L : ℂ) * z) - (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)

def balanceRadius (k : ℕ) (α : ℝ) : ℝ :=
  Real.rpow ((5 : ℝ) / (2 * α)) (1 / (2 * (k : ℝ)))

/-- Claim 3108: the horizontal Dini boundary bound on the normalized annulus. -/
def claim3108 : Prop :=
  ∀ (k : ℕ) (α ε K Y : ℝ),
    1 ≤ k → 0 < α → 0 < ε →
    K > balanceRadius k α + ε → 0 < Y → Y < 1 / 2 →
    ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L →
        ∀ x : ℝ,
          (balanceRadius k α + ε) *
              Real.rpow L (1 / (2 * (k : ℝ))) ≤ x →
          x ≤ K * Real.rpow L (1 / (2 * (k : ℝ))) →
          ‖diniTerm L ((x : ℂ) + (Y : ℂ) * Complex.I)‖ ≥
              x * Real.sinh (L * Y) - (1 / 2 : ℝ) * Real.cosh (L * Y) ∧
          ‖diniTerm L ((x : ℂ) - (Y : ℂ) * Complex.I)‖ ≥
              x * Real.sinh (L * Y) - (1 / 2 : ℝ) * Real.cosh (L * Y) ∧
          x * Real.sinh (L * Y) - (1 / 2 : ℝ) * Real.cosh (L * Y) ≥
            x * Real.sinh (L * Y) / 2

end
end MathlibPlus.Open.Research.Batch_01a00468_Dini
