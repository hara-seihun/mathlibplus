import Mathlib

open CategoryTheory

namespace MathlibPlus.Algebra

/-- Claim 11674: every unital ring endomorphism of `ℤ` is the identity. -/
theorem intRingEndHom_eq_id (f : ℤ →+* ℤ) : f = RingHom.id ℤ := by
  ext z
  simpa using f.map_intCast z

/-- Claim 11674, scheme-theoretic dual: every endomorphism of `Spec ℤ` is the
identity. -/
theorem specIntSchemeEnd_eq_id
    (f : AlgebraicGeometry.Spec (CommRingCat.of ℤ) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of ℤ)) :
    f = 𝟙 _ := by
  rw [← AlgebraicGeometry.Spec.map_preimage f]
  rw [← AlgebraicGeometry.Spec.map_id]
  apply congrArg AlgebraicGeometry.Spec.map
  apply CommRingCat.hom_ext
  exact intRingEndHom_eq_id (AlgebraicGeometry.Spec.preimage f).hom

end MathlibPlus.Algebra
