import Mathlib

/-!
Formalization of admitted claim 10386.  The source does not specify a
manifold, a form bundle, or a particular zeta operator, so the declaration
records the exact algebraic implication of flow invariance for a nonzero
resonance vector.  Horizontality is not needed for that implication.
-/

namespace MathlibPlus.Analysis.BasicFormResonance

/-- A nonzero vector fixed by a flow generator cannot have a nonzero scalar
resonance eigenvalue. -/
theorem basic_nonzero_resonance_is_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L : E →ₗ[ℂ] E) {u : E} {spectralValue : ℂ}
    (hu : u ≠ 0) (hbasic : L u = 0)
    (hres : L u = spectralValue • u) :
    spectralValue = 0 := by
  have h : spectralValue • u = 0 := by rw [← hres, hbasic]
  exact (smul_eq_zero.mp h).resolve_right hu

end MathlibPlus.Analysis.BasicFormResonance
