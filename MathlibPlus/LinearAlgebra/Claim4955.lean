import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim4955

open Set Submodule

/-- An invertible ambient coordinate change carries the span of every selected
family onto the span of its transformed family. -/
theorem span_map_claim4955
    {R V W ι : Type*} [DivisionRing R]
    [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (e : V ≃ₗ[R] W) (v : ι → V) (s : Set ι) :
    (span R (v '' s)).map (e : V →ₗ[R] W) =
      span R ((e ∘ v) '' s) := by
  rw [Submodule.map_span]
  rw [Set.image_image]
  rfl

/-- The span rank (finite dimension) is unchanged by the same coordinate
change. -/
theorem span_finrank_map_claim4955
    {R V W ι : Type*} [DivisionRing R]
    [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (e : V ≃ₗ[R] W) (v : ι → V) (s : Set ι) :
    Module.finrank R ((span R (v '' s)).map (e : V →ₗ[R] W)) =
      Module.finrank R (span R (v '' s)) :=
  LinearEquiv.finrank_map_eq e (span R (v '' s))

/-- Linear independence of a selected family is invariant in both directions
under an ambient linear equivalence. -/
theorem linearIndependent_iff_map_claim4955
    {R V W ι : Type*} [DivisionRing R]
    [AddCommGroup V] [AddCommGroup W]
    [Module R V] [Module R W]
    (e : V ≃ₗ[R] W) (v : ι → V) :
    LinearIndependent R v ↔ LinearIndependent R (e ∘ v) := by
  constructor
  · intro hv
    exact hv.map' (e : V →ₗ[R] W) (by simp)
  · intro hv
    have h := hv.map' (e.symm : W →ₗ[R] V) (by simp)
    simpa [Function.comp_def] using h

end MathlibPlus.LinearAlgebra.Claim4955
