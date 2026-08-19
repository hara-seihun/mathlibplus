import Mathlib

namespace MathlibPlus.Open.Analysis.Claim13463

/-- The critical-line action has squared norm exactly one half of the input
squared norm. -/
def criticalLineHalfNorm : Prop :=
  ∀ (t X Y : ℝ),
    let theta : ℝ := t * Real.log 2
    let yEven : ℝ :=
      (Real.cos theta * X + Real.sin theta * Y) / Real.sqrt 2
    let yOdd : ℝ :=
      (-Real.sin theta * X + Real.cos theta * Y) / Real.sqrt 2
    yEven ^ 2 + yOdd ^ 2 = (X ^ 2 + Y ^ 2) / 2

end MathlibPlus.Open.Analysis.Claim13463
