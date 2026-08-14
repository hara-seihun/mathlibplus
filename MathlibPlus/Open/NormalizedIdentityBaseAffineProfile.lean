import Mathlib

namespace MathlibPlus.Open

/--
The normalized identity-base affine profile from Claim 39765.  The map `f` is
required to have exactly the displayed affine formula; no additional
properties of the arbitrary maps are imposed.
-/
def normalized_identity_base_affine_profile
    {d s : ℕ} {O : Type*} [Fintype O] [Group O]
    (hO : Odd (Fintype.card O))
    (A : ((Fin s → ZMod 2) × O) →
      ((Fin d → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2)))
    (c : ((Fin s → ZMod 2) × O) → (Fin d → ZMod 2))
    (f : ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O)) →
      ((Fin d → ZMod 2) × ((Fin s → ZMod 2) × O))) : Prop :=
  A (0, 1) = LinearEquiv.refl (ZMod 2) (Fin d → ZMod 2) ∧
    c (0, 1) = 0 ∧
    ∀ v e o, f (v, (e, o)) = (A (e, o) v + c (e, o), (e, o))

end MathlibPlus.Open
