import Mathlib

namespace MathlibPlus.Algebra.AffineConjugation

/--
Formalization of admitted claim 30793.  The linear parts are represented by
additive endomorphisms; the formula is uniform in the index `g` and has no
monomiality or transitivity hypothesis.
-/
theorem affine_conjugation_removes_additive_part_30793
    {G M : Type*} [AddCommGroup M] (ρ : G → M →+ M) (s : M) :
    ∀ g : G, ∀ v : M,
      let b : M := s - ρ g s
      let A : M → M := fun x => ρ g x + b
      let τ : M → M := fun x => x + s
      let τInv : M → M := fun x => x - s
      τInv (A (τ v)) = ρ g v := by
  intro g v
  dsimp
  rw [(ρ g).map_add]
  abel

end MathlibPlus.Algebra.AffineConjugation
