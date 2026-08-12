import Mathlib

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MathlibPlus.Analysis

/-- Claim 3845: extended-nonnegative Mellin-tail tightness predicate for two
real-valued function sequences. -/
def mellinTailTight_claim3845 (f g : ℕ → ℝ → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R →
    Tendsto
      (fun A : ℝ =>
        ⨆ j : ℕ, ∫⁻ t in {t : ℝ | |t| > A},
          ENNReal.ofReal (Real.exp (R * |t|) * (|f j t| + |g j t|)))
      atTop (𝓝 (0 : ℝ≥0∞))

end MathlibPlus.Analysis
