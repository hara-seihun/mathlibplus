import Mathlib

namespace MathlibPlus.Open.NewResearch2.C0111

noncomputable section

private def nontrivialPositiveZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im

/-- Claim 1718: the zero-free assertion with denominator `4.852 = 1213/250`. -/
def denominator4852ZeroFree_newResearch2_claim1718 : Prop :=
  ∀ (t σ : ℝ), 2 ≤ t →
    σ > 1 - 1 / ((1213 / 250 : ℝ) * Real.log t) →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Claim 1730: the verified low-height splice and the denominator-4.83 boundary at `t=2`. -/
def lowHeightCriticalLineSplice_newResearch2_claim1730 : Prop :=
  (3 * (10 : ℝ) ^ 12 < (3000175332801 : ℝ)) ∧
    (∀ ρ : ℂ, nontrivialPositiveZero ρ →
      ρ.im ≤ (3000175332801 : ℝ) → ρ.re = 1 / 2) ∧
    (1 / 2 + 201305 / 1000000 : ℝ) <
      1 - 1 / ((483 / 100 : ℝ) * Real.log 2) ∧
    (∀ ρ : ℂ, nontrivialPositiveZero ρ →
      ρ.im < 3 * (10 : ℝ) ^ 12 → ρ.re = 1 / 2)

end

end MathlibPlus.Open.NewResearch2.C0111
