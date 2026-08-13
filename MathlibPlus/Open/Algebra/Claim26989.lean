import Mathlib

namespace MathlibPlus.Open.Algebra

/-- Faithful registry node for the affine-color collapse criterion.  The two
color equations and the orientation-pair multiplicity are explicit because
the packet does not provide their source definitions. -/
def affineColorCollapseCriterion_claim26989 : Prop :=
  ∀ (m : ℕ) (Orientation : Type*) (pair : Orientation)
    (multiplicity : Orientation → ℕ)
    (rotationColor reflectionColor :
      Orientation → (ZMod m)ˣ → ZMod m → Fin 3 → Prop),
    (multiplicity pair = 2 ↔
      ¬ ∃ (u : (ZMod m)ˣ) (t : ZMod m) (j : Fin 3),
        rotationColor pair u t j ∧ reflectionColor pair u t j) ∧
    (multiplicity pair = 1 ↔
      ∃ (u : (ZMod m)ˣ) (t : ZMod m) (j : Fin 3),
        rotationColor pair u t j ∧ reflectionColor pair u t j)

end MathlibPlus.Open.Algebra
