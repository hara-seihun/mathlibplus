import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace MathlibPlus.Open.Analysis

/-- Claim 18893: for every real `p > 1`, all complex zeros of
`B + 2 cosh(q log p)` lie on the imaginary axis exactly when `|B| ≤ 2`.
The zero condition and the axis condition are written explicitly over `ℂ`;
no branch or growth convention beyond the real logarithm of `p` is added. -/
def sharpLocalTemperedZeroThreshold_claim18893 : Prop :=
  ∀ (p : ℝ),
    1 < p →
    ∀ (B : ℝ),
      (∀ (q : ℂ),
        (B : ℂ) + 2 * Complex.cosh (q * (Real.log p : ℂ)) = 0 →
          q.re = 0) ↔
        |B| ≤ 2

end MathlibPlus.Open.Analysis
