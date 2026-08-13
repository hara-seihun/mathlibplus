import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim18067

/-- The rowwise bidiagonal Euler boundary operator. -/
noncomputable def bidiagonalEulerBoundary (f : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (((n : ℂ) + (1 : ℂ) / 2 + z) * f (n + 1) z) - (n : ℂ) * f n z

end MathlibPlus.Analysis.Claim18067

namespace MathlibPlus.Analysis.Claim22419

/-- The moving mollifier coordinate β(U). -/
noncomputable def beta (t y U : ℝ) : ℝ :=
  (1 + y) / 2 + (t / 4) * Real.log U

/-- The complex moving mollifier term, with the cutoff coordinate restricted to U > 0. -/
noncomputable def T₂ (t y : ℝ) (U : {u : ℝ // 0 < u}) (c₂ : ℂ) : ℂ :=
  c₂ * (Real.rpow 2 (-beta t y U) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (U : ℂ) * Real.log 2)

end MathlibPlus.Analysis.Claim22419
