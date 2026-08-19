import Mathlib

namespace MathlibPlus.Analysis.Claim4537

/-- The polyharmonic saddle constant for a positive integer order. -/
noncomputable def polyharmonicSaddleConstant_claim4537
    (m : ℕ) (_hm : 0 < m) : ℝ :=
  (2 * (m : ℝ) - 1) *
    Real.rpow (2 * (m : ℝ))
      (-(2 * (m : ℝ)) / (2 * (m : ℝ) - 1)) *
    Real.sin (Real.pi / (4 * (m : ℝ) - 2))

end MathlibPlus.Analysis.Claim4537
