import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-!
Claim 13447.  The source leaves the scalar domain and branch convention for
`2^(1-z)` implicit.  The literal algebraic shift is recorded over `ℂ` using
`Complex.cpow`; no nonvanishing-denominator hypothesis is added, since the
identity is valid with Lean's total division operation as well.
-/

/-- The degree-one scalar local pullback factor and its shift. -/
theorem scalarLocalPullbackFactor_claim13447 (k s : ℂ) :
    let A : ℂ → ℂ := fun z => Complex.cpow 2 (1 - z) / (z + k)
    let α : ℂ := s + k - 1
    A (s - 1) = Complex.cpow 2 (2 - s) / (s + k - 1) ∧
      A (s - 1) = Complex.cpow 2 (2 - s) / α := by
  dsimp
  constructor
  · rw [show 1 - (s - 1) = 2 - s by ring]
    rw [show s - 1 + k = s + k - 1 by ring]
  · rw [show 1 - (s - 1) = 2 - s by ring]
    rw [show s - 1 + k = s + k - 1 by ring]

end MathlibPlus.Algebra
