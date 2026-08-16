import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.PolarizedTuranClaim4225

/-- The Poisson coefficient sequence used by source group `C-0302`. -/
noncomputable def poissonWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (n.factorial : ℝ)

/-- The bilinear polarized Turán form, with no conjugation in either factor. -/
noncomputable def polarizedTuranForm (x : ℝ) (u v : ℕ → ℂ) : ℂ :=
  ∑' n : ℕ,
    (poissonWeight x n : ℂ) *
      (u n * v (n + 2) - u (n + 1) * v (n + 1))

/-- The associated scalar is the diagonal value of the bilinear form. -/
noncomputable def turanScalar (x : ℝ) (u : ℕ → ℂ) : ℂ :=
  polarizedTuranForm x u u

end MathlibPlus.Open.Analysis.PolarizedTuranClaim4225
