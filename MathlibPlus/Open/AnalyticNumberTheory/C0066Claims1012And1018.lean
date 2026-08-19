import Mathlib

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- Claim 1012: the large-height Littlewood zero-free region, with the
real variables embedded in the complex argument of `riemannZeta`. -/
noncomputable def largeHeightLittlewoodRegion_claim1012 : Prop :=
  ∀ (t σ : ℝ),
    3 ≤ t →
      σ > 1 - Real.log (Real.log t) / ((19.62 : ℝ) * Real.log t) →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

/-- Claim 1018: the exact rational increment decomposition and the resulting
arithmetic landing at the target amplitude. -/
noncomputable def exactFiniteInductionToTargetAmplitude_claim1018 : Prop :=
  let ε : ℝ := 10 ^ (-100 : ℤ)
  let q : ℕ :=
    1100463757436658956817582065434015202686716235956156643532717557833222076447456487112799075786517
  let r : ℝ := 4336337 / (4543539 * 10 ^ (100 : ℕ))
  (1 / (4.8594 : ℝ) - 1 / 4.862 = (q : ℝ) * ε + r) ∧
    0 < r ∧ r < ε ∧
    1 / (4.862 : ℝ) + (q : ℝ) * ε + r = 1 / 4.8594

end MathlibPlus.Open.AnalyticNumberTheory
