import MathlibPlus.Basic

namespace MathlibPlus.Arithmetic

/-- The affine reflection of an integer interval is `i ↦ a+b-1-i`, and is
involutive. -/
theorem intervalReflectionFormula_claim17917 (a b i : ℤ) :
    let r_ab : ℤ → ℤ := fun j => a + b - 1 - j
    r_ab i = a + b - 1 - i ∧ r_ab (r_ab i) = i := by
  dsimp
  constructor
  · rfl
  · ring

/-- In split coordinates `0 ≤ k < ℓ`, interval reflection is the map
`k ↦ ℓ-1-k`, which remains in the interval and is involutive. -/
theorem splitIntervalReflection_claim17917 (ℓ k : ℕ) (hk : k < ℓ) :
    ℓ - 1 - k < ℓ ∧ ℓ - 1 - (ℓ - 1 - k) = k := by
  omega

end MathlibPlus.Arithmetic
