import Mathlib

open scoped Interval

namespace MathlibPlus.Open.NewResearch2.R0133

noncomputable section

/-- Claim 18170: the endpoint-deficit matrix is strictly sign-regular with
 the stated checkerboard determinant signature. -/
def claim18170_strictSignRegularityEndpointDeficit : Prop :=
  ∀ (r : ℕ), 1 ≤ r →
    ∀ (n : Fin r → ℕ), StrictMono n →
      ∀ (c : Fin r → ℝ), StrictMono c →
        (∀ j : Fin r, 0 < c j) →
          0 < (-1 : ℝ) ^ (r * (r - 1) / 2) *
            Matrix.det (fun i j : Fin r =>
              (∫ x in (n i : ℝ)..((n i : ℝ) + 1),
                Real.exp (-(c j) * x ^ 2)) -
                Real.exp (-(c j) * ((n i : ℝ) + 1) ^ 2))

end

end MathlibPlus.Open.NewResearch2.R0133
