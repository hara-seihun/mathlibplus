import MathlibPlus.Open.Analysis.AbelBatch

open Filter

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- Claim 8852: the detrended coefficient count and its slow-oscillation
hypotheses, with `H` taken from the exact Jacobi counting carrier. -/
def claim8852 (a : JacobiIndex → ℝ) : Prop :=
  let h : ℝ → ℝ := fun x =>
    logScaleCount a x - x / 2 + (1 / 2 : ℝ) * Real.log (4 * Real.pi)
  (∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in Filter.atTop, |h x| ≤ C) ∧
    Filter.Tendsto
      (fun δ : ℝ =>
        Filter.limsup
          (fun x : ℝ =>
            sSup (Set.range (fun u : {u : ℝ // |u| ≤ δ} =>
              |h (x + u.1) - h x|)))
          Filter.atTop)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0)

end

end MathlibPlus.Open.Analysis
