import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim6058

/-- The relative derivative from the admitted normalized-permutation claim. -/
def relativeDerivativeValue {H : Type*} [AddGroup H] (g : H ≃ H)
    (hg : g 0 = 0) (k h : H) : H :=
  g.symm (g (h + k) - g k)

/-- The relative derivative is a permutation of the base set. -/
theorem relativeDerivative_bijective {H : Type*} [AddGroup H] (g : H ≃ H)
    (hg : g 0 = 0) (k : H) :
    Function.Bijective (relativeDerivativeValue g hg k) := by
  constructor
  · intro h₁ h₂ h
    have h' := congrArg g h
    simp only [relativeDerivativeValue, Equiv.apply_symm_apply] at h'
    have h'' : g (h₁ + k) = g (h₂ + k) := sub_left_injective h'
    exact add_right_cancel (g.injective h'')
  · intro y
    refine ⟨g.symm (g y + g k) - k, ?_⟩
    simp [relativeDerivativeValue]

/-- Normalization at the zero increment. -/
theorem relativeDerivative_zero {H : Type*} [AddGroup H] (g : H ≃ H)
    (hg : g 0 = 0) (k : H) :
    relativeDerivativeValue g hg k 0 = 0 := by
  have hzero : g.symm 0 = 0 := by
    calc
      g.symm 0 = g.symm (g 0) := by rw [hg]
      _ = 0 := g.symm_apply_apply 0
  simp [relativeDerivativeValue, hzero]

end MathlibPlus.GroupTheory.Claim6058
