import MathlibPlus.AxlerMajorant

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- Claim 633: the small-range inequalities for the canonical fixed
`6097.2` majorant.  The eight summands are recorded separately on `(1,2)`,
and real prime counts use the inclusive floor convention. -/
def smallRangeIntervalBound : Prop :=
  let primeCountingReal : ℝ → ℕ := fun x => Nat.primeCounting (Nat.floor x)
  let t₁ : ℝ → ℝ := fun x => x / Real.log x
  let t₂ : ℝ → ℝ := fun x => x / Real.log x ^ 2
  let t₃ : ℝ → ℝ := fun x => 2 * x / Real.log x ^ 3
  let t₄ : ℝ → ℝ := fun x => 6.024334 * x / Real.log x ^ 4
  let t₅ : ℝ → ℝ := fun x => 24.024334 * x / Real.log x ^ 5
  let t₆ : ℝ → ℝ := fun x => 120.12167 * x / Real.log x ^ 6
  let t₇ : ℝ → ℝ := fun x => 720.73002 * x / Real.log x ^ 7
  let t₈ : ℝ → ℝ := fun x => (30486 / 5 : ℝ) * x / Real.log x ^ 8
  (∀ x : ℝ, 2 ≤ x → x ≤ 47 →
      (29.8 : ℝ) < MathlibPlus.AxlerMajorant.predecessorBound x ∧
        (15 : ℝ) < 29.8 ∧
        (primeCountingReal x : ℝ) ≤ 15) ∧
    ∀ x : ℝ, 1 < x → x < 2 →
      0 < t₁ x ∧ 0 < t₂ x ∧ 0 < t₃ x ∧ 0 < t₄ x ∧
        0 < t₅ x ∧ 0 < t₆ x ∧ 0 < t₇ x ∧ 0 < t₈ x ∧
        (primeCountingReal x : ℝ) < MathlibPlus.AxlerMajorant.predecessorBound x

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
