import MathlibPlus.Open.Analysis.GammaReadout

namespace MathlibPlus.Open.Analysis

open scoped Interval

noncomputable def gammaRemainder50164 (m : ℕ) (q L : ℝ) : ℂ :=
  iteratedDeriv m (gammaG q) 0 -
    ∫ v in Set.Ioc (0 : ℝ) L,
      (Real.exp (-v) : ℂ) * gammaPhi m q (v : ℂ)

/-- Claim 50164: the cell cutoff bound is uniform in the cell variable. -/
def claim50164 : Prop :=
  ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℝ) (n : ℕ) (M : ℝ),
      (n : ℝ) < x → x < (n : ℝ) + 1 → 1 ≤ M →
        let q : ℝ := (Real.pi * x ^ 2)⁻¹
        let L : ℝ := M * Real.pi * ((n : ℝ) + 1) ^ 2
        q * L = M * ((n : ℝ) + 1) ^ 2 / x ^ 2 ∧
          M ≤ q * L ∧
            ‖gammaRemainder50164 (2 * j) q L‖ ≤
              C * Real.rpow M (-(5 / 4 : ℝ)) *
                  (1 + Real.log M + Real.log ((n : ℝ) + 1)) ^ (2 * j) +
                C * Real.exp (-M * Real.pi * ((n : ℝ) + 1) ^ 2 / 2) *
                  (1 + Real.log M + Real.log ((n : ℝ) + 1)) ^ (2 * j)

end MathlibPlus.Open.Analysis
