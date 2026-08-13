import Mathlib

namespace MathlibPlus.Analysis.Claim47717

/-- Claim 47717: the displayed two-exponential factorization is an exact
algebraic identity. -/
theorem exponential_factorization_claim47717 (a q t : ℝ) :
    Real.exp (-a * t - q * Real.exp (-t)) +
        Real.exp (a * t - q * Real.exp t) =
      Real.exp (-a * t - q * Real.exp (-t)) *
        (1 + Real.exp (2 * a * t - q * (Real.exp t - Real.exp (-t)))) := by
  rw [mul_add, mul_one]
  have h : (-a * t - q * Real.exp (-t)) +
      (2 * a * t - q * (Real.exp t - Real.exp (-t))) =
      a * t - q * Real.exp t := by
    ring
  rw [← Real.exp_add]
  rw [h]

end MathlibPlus.Analysis.Claim47717
