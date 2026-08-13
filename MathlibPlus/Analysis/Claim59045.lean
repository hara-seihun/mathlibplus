import Mathlib

namespace MathlibPlus.Analysis.Claim59045

/-- The two-sided seam-patch obstruction in claim 59045.  Continuity is
retained as a source hypothesis, although the contradiction is already
pointwise by the triangle inequality. -/
theorem twoSidedSeamPatch
    (fN fPrev g : ℝ → ℝ) (z : ℝ)
    (_hg : Continuous g)
    (hleft : |fN z - g z| ≤ (1 : ℝ) / 200000000)
    (hright : |g z - fPrev z| ≤ (1 : ℝ) / 200000000)
    (hjump : |fN z - fPrev z| > (1 : ℝ) / 100000000) :
    False := by
  have htri : |fN z - fPrev z| ≤
      |fN z - g z| + |g z - fPrev z| := by
    calc
      |fN z - fPrev z| = |(fN z - g z) + (g z - fPrev z)| := by ring_nf
      _ ≤ |fN z - g z| + |g z - fPrev z| := abs_add_le _ _
  have hsum : |fN z - g z| + |g z - fPrev z| ≤
      (1 : ℝ) / 100000000 := by
    linarith
  linarith

end MathlibPlus.Analysis.Claim59045
