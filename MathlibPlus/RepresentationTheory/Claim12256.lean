import Mathlib

/-!
# Claim 12256: a nontrivial one-dimensional character has no invariants

The one-dimensional representation is made explicit as scalar multiplication by
`(χ g : ℂ)`.  Thus its invariant subspace is represented by the scalars fixed by
that action.
-/

namespace MathlibPlus.RepresentationTheory.Claim12256

/-- A nontrivial complex-valued one-dimensional character has only the zero
invariant scalar. -/
theorem invariant_scalar_eq_zero {G : Type*} [Group G] (χ : G →* ℂˣ)
    (hχ : ∃ g : G, χ g ≠ 1) {z : ℂ}
    (hz : ∀ g : G, (χ g : ℂ) * z = z) : z = 0 := by
  obtain ⟨g, hg⟩ := hχ
  by_contra hz0
  have hmul : ((χ g : ℂ) - 1) * z = 0 := by
    calc
      ((χ g : ℂ) - 1) * z = (χ g : ℂ) * z - 1 * z := by ring
      _ = 0 := by rw [hz g]; ring
  have hsub : (χ g : ℂ) - 1 = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hz0
  have hval : (χ g : ℂ) = 1 := sub_eq_zero.mp hsub
  apply hg
  exact Units.ext hval

end MathlibPlus.RepresentationTheory.Claim12256
