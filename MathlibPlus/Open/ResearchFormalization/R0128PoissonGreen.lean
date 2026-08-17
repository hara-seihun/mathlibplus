import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0128

/-- Claim 18140: the normalized Poisson fields satisfy the stated Green
identity on the nonresonant, distinct-square-root domain. -/
noncomputable def poissonGreenIdentity_18140 : Prop :=
  ∀ (x y : ℝ),
    Real.sin (Real.pi * x) ≠ 0 →
    Real.sin (Real.pi * y) ≠ 0 →
    x ^ 2 ≠ y ^ 2 →
      (∫ r : ℝ in (0 : ℝ)..Real.pi,
        (Real.sin (x * r) / Real.sin (Real.pi * x)) *
          (Real.sin (y * r) / Real.sin (Real.pi * y))) =
        (y * Real.cot (Real.pi * y) - x * Real.cot (Real.pi * x)) /
          (x ^ 2 - y ^ 2)

end MathlibPlus.Open.ResearchFormalization.R0128
