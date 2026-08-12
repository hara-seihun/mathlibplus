import Mathlib.Tactic

namespace MathlibPlus.Analysis.Claim48756

/-!
Formalization of the pointwise selector identity in claim 48756.  The
independence of the three signs is probabilistic context; the displayed
identity itself is pointwise, so the Lean statement records the exact sign
values and does not introduce a probability space.
-/

/-- The two-channel selector agrees with its affine Rademacher expansion. -/
theorem twoChannelSelectorFormula
    (X Y₁ Y₂ : ℝ)
    (hX : X = -1 ∨ X = 1)
    (hY₁ : Y₁ = -1 ∨ Y₁ = 1)
    (hY₂ : Y₂ = -1 ∨ Y₂ = 1) :
    let g : ℝ := if X = -1 then Y₁ else -Y₂
    g = (Y₁ - Y₂) / 2 - X * (Y₁ + Y₂) / 2 ∧
      (X = -1 → g = Y₁) ∧ (X = 1 → g = -Y₂) := by
  dsimp
  rcases hX with rfl | rfl
  · simp only [if_pos]
    constructor
    · ring
    constructor
    · intro
      simp
    · intro h
      norm_num at h
  · have hne : (1 : ℝ) ≠ -1 := by norm_num
    simp only [if_neg hne]
    constructor
    · ring
    constructor
    · intro h
      norm_num at h
    · intro
      simp

end MathlibPlus.Analysis.Claim48756
