import Mathlib

open scoped Interval

namespace MathlibPlus.Open.NewResearch2.R0133

noncomputable section

/-- Claim 18172: the reflected heat-scale reparameterization has the strict
checkerboard signature on every ordered positive minor. -/
def claim18172_reflectedSheetCheckerboardSignature : Prop :=
  ∀ (k : ℕ), 1 ≤ k →
    ∀ (n : Fin k → ℕ), StrictMono n →
      ∀ (r : Fin k → ℝ), StrictMono r →
        (∀ j : Fin k, 0 < r j) →
          0 < (-1 : ℝ) ^ (k * (k - 1) / 2) *
            Matrix.det (fun i j : Fin k =>
              (∫ x in (n i : ℝ)..((n i : ℝ) + 1),
                Real.exp (-(Real.pi * r j) * x ^ 2)) -
                Real.exp (-(Real.pi * r j) * ((n i : ℝ) + 1) ^ 2))

end

end MathlibPlus.Open.NewResearch2.R0133
