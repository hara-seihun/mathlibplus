import Mathlib

namespace MathlibPlus.Algebra

/-- A finitely generated ideal has finitely generated conormal module. -/
theorem conormal_finite_of_fg_claim23502 {A : Type*} [CommRing A]
    (K : Ideal A) (hK : K.FG) :
    Module.Finite (A ⧸ K) K.Cotangent := by
  letI : Module.Finite A K := Module.Finite.of_fg hK
  letI : Module.Finite A K.Cotangent :=
    Module.Finite.quotient A (K • (⊤ : Submodule A K))
  exact Module.Finite.of_restrictScalars_finite A (A ⧸ K) K.Cotangent

end MathlibPlus.Algebra
