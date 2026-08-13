import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- A normalized permutation profile on a cyclic-four fibre which depends only
on one cyclic-three coordinate cannot move a Cayley connection set. -/
def cyclicFourTernaryCosetProfilesFixConnectionSets : Prop :=
  ∀ (H : Type*) [Group H]
    (σ : Multiplicative (ZMod 3) →
      Equiv.Perm (Multiplicative (ZMod 4))),
    σ 1 = Equiv.refl (Multiplicative (ZMod 4)) →
    let G :=
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 3)) × H
    let f : G → G := fun x =>
      ((σ x.1.2 x.1.1, x.1.2), x.2)
    ∀ (S T : Set G),
      (∀ x y : G,
        x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T) →
      S = T

end MathlibPlus.Open.GraphTheory
