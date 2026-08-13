import Mathlib

namespace MathlibPlus.Analysis.Claim2005

/-- On the half-line `ξ > 1`, multiplication by `ξ - 1` preserves the sign
of the constant-phase factor.  This is the kernel-checked threshold core of
`Q(ξ) = (A(ξ) - 2) (ξ - 1)`. -/
theorem constant_phase_threshold_sign_claim2005
    (ξ A : ℝ) (hξ : 1 < ξ) :
    let Q := (A - 2) * (ξ - 1)
    (Q ≥ 0 ↔ A ≥ 2) ∧ (Q = 0 ↔ A = 2) ∧ (Q > 0 ↔ A > 2) := by
  dsimp
  have hpos : 0 < ξ - 1 := by linarith
  constructor
  · constructor
    · intro hQ
      nlinarith
    · intro hA
      nlinarith
  constructor
  · constructor
    · intro hQ
      nlinarith
    · intro hA
      simp [hA]
  · constructor
    · intro hQ
      nlinarith
    · intro hA
      nlinarith

end MathlibPlus.Analysis.Claim2005
