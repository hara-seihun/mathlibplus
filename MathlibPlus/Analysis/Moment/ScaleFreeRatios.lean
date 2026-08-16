import MathlibPlus.Basic

/-!
# Scale-free chamber ratios

Exact definitions from admitted claim 350 in source record `C-0021`.  The source
states the two quotients without extra hypotheses, so they are totalized using Lean's
field division and no positivity or nonvanishing assumption is added.
-/

namespace MathlibPlus.Analysis.Moment.ScaleFreeRatios

/-- The first scale-free chamber ratio `R = m₁² / (m₀ m₂)`. -/
noncomputable def ratioR (m : ℕ → ℝ) : ℝ :=
  m 1 ^ 2 / (m 0 * m 2)

/-- The second scale-free chamber ratio `S = m₁ m₃ / m₂²`. -/
noncomputable def ratioS (m : ℕ → ℝ) : ℝ :=
  m 1 * m 3 / m 2 ^ 2

end MathlibPlus.Analysis.Moment.ScaleFreeRatios
