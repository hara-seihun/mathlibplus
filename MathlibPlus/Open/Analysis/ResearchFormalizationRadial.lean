import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The radial point and phase from the admitted exact-coordinate claim. -/
private noncomputable def radialZ (S k : ℕ) (u y : ℝ) : ℂ :=
  (Real.sqrt ((S : ℝ) ^ 2 * Real.exp (u / (k : ℝ)) - y ^ 2) : ℂ) +
    (y : ℂ) * Complex.I

private noncomputable def radialTheta (S k : ℕ) (u y : ℝ) : ℝ :=
  2 * (k : ℝ) * Real.arcsin
    (y / ((S : ℝ) * Real.exp (u / (2 * (k : ℝ)))))

/-- Exact radial identities and the uniform bounded-height phase derivative. -/
def exactRadialCoordinatesClaim : Prop :=
  (∀ (k S : ℕ) (u y : ℝ),
    0 < k →
    0 < S →
    y ^ 2 ≤ (S : ℝ) ^ 2 * Real.exp (u / (k : ℝ)) →
      ‖radialZ S k u y / (S : ℂ)‖ ^ (2 * k) = Real.exp u ∧
        (radialZ S k u y / (S : ℂ)) ^ (2 * k) =
          (Real.exp u : ℂ) * Complex.exp
            ((radialTheta S k u y : ℂ) * Complex.I)) ∧
  (∀ (M : ℝ),
    0 < M →
      ∃ (C : ℝ),
        0 < C ∧
          ∃ (S₀ : ℕ),
            1 ≤ S₀ ∧
              ∀ (k S : ℕ),
                0 < k →
                S₀ ≤ S →
                  ∀ (u y : ℝ),
                    |u| ≤ M →
                    |y| ≤ M →
                      |deriv (fun t : ℝ => radialTheta S k t y) u| ≤ C / (S : ℝ))

end MathlibPlus.Open.Analysis
