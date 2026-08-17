import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The prime Dirichlet sum used by the weighted Euler approximant. -/
noncomputable def primeCumulantSum
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ) (Y : ℕ) (z : ℂ) : ℂ :=
  ∑' p : {p : ℕ // Nat.Prime p},
    (q Y p : ℂ) * Complex.cpow (p.1 : ℂ) (-z)

/-- The weighted Euler approximant with the principal complex logarithm branch. -/
noncomputable def weightedEulerApproximant
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ) (Y : ℕ) (z : ℂ) : ℂ :=
  Complex.exp
    (∑' p : {p : ℕ // Nat.Prime p},
      (q Y p : ℂ) *
        Complex.log (1 - Complex.cpow (p.1 : ℂ) (-z)))

/-- The first-cumulant remainder in the logarithmic Euler decomposition. -/
noncomputable def firstCumulantRemainder
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ)
    (σ : ℝ) (Y : ℕ) (t : ℝ) : ℝ :=
  Real.log ‖weightedEulerApproximant q Y
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
    (primeCumulantSum q Y
      ((σ : ℂ) + (t : ℂ) * Complex.I)).re

/-- Claim 11412: bounded prime weights admit a uniformly bounded first-cumulant
remainder for the weighted Euler approximant. -/
def claim11412 : Prop :=
  ∀ (c σ : ℝ)
    (q : ℕ → {p : ℕ // Nat.Prime p} → ℝ),
    (1 < c ∧ c < 3 / 2 ∧ σ = 2 - c ∧
      1 / 2 < σ ∧ σ < 1) →
    (∃ M : ℝ, ∀ Y p, 0 ≤ q Y p ∧ q Y p ≤ M) →
    ∃ C : ℝ, ∀ (Y : ℕ) (t : ℝ),
      Real.log ‖weightedEulerApproximant q Y
          ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
          -(primeCumulantSum q Y
              ((σ : ℂ) + (t : ℂ) * Complex.I)).re +
            firstCumulantRemainder q σ Y t ∧
        |firstCumulantRemainder q σ Y t| ≤ C

end

end MathlibPlus.Open.ResearchFormalization
