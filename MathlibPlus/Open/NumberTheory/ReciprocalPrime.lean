import MathlibPlus.PrimeMertens

namespace MathlibPlus.Open.NumberTheory.ReciprocalPrime

/-- Claim 617: every real `x ≥ 286` satisfies the strict rational upper bound
for the reciprocal-prime Mertens error.  The decimal equality is retained at
its full displayed precision. -/
def rationalStrictUpperBound : Prop :=
  ∃ B : ℝ,
    MathlibPlus.PrimeMertens.IsMeisselMertensConstant B ∧
      ∀ x : ℝ, 286 ≤ x →
        MathlibPlus.PrimeMertens.mertensError B x <
            (121801 : ℝ) / (250000 * (Real.log x) ^ 2) ∧
          (121801 : ℝ) / (250000 * (Real.log x) ^ 2) =
            (0.487204 : ℝ) / (Real.log x) ^ 2

end MathlibPlus.Open.NumberTheory.ReciprocalPrime
