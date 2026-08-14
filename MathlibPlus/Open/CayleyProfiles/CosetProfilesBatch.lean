import Mathlib

namespace MathlibPlus.Open.CayleyProfiles.Batch

abbrev C4 := ZMod 4
abbrev C3Cubed := Fin 3 → ZMod 3
abbrev ProfileGroup := C4 × C3Cubed

/-- The lift of a quotient automorphism that is the identity on the `C₄` factor. -/
def quotientLift (β : C3Cubed ≃+ C3Cubed) : ProfileGroup ≃+ ProfileGroup where
  toFun := fun x => (x.1, β x.2)
  invFun := fun x => (x.1, β.symm x.2)
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp
  map_add' := by
    intro x y
    simp

/-- A normalized Cayley-presentation isomorphism in the additive convention. -/
def CayleyPresentationIso
    (S T : Set ProfileGroup) (f : ProfileGroup ≃ ProfileGroup) : Prop :=
  ∀ x y : ProfileGroup, y - x ∈ S ↔ f y - f x ∈ T

/-- The coset quotient component induced by a map. -/
def HasQuotientMap
    (f : ProfileGroup ≃ ProfileGroup) (β : C3Cubed ≃+ C3Cubed) : Prop :=
  ∀ a : C4, ∀ v : C3Cubed, (f (a, v)).2 = β v

/-- Inverse-closedness of an additive Cayley connection set. -/
def InverseClosed (S : Set ProfileGroup) : Prop :=
  ∀ x : ProfileGroup, x ∈ S ↔ -x ∈ S

/-- Correct the quotient component of a normalized map. -/
def quotientCorrected
    (f : ProfileGroup ≃ ProfileGroup) (β : C3Cubed ≃+ C3Cubed) :
    ProfileGroup ≃ ProfileGroup :=
  f.trans (quotientLift β).toEquiv.symm

/-- Claim 31472: after correcting the actual quotient component, a normalized
map has identity quotient and is a fibre profile fixing the identity fibre. -/
def claim31472 : Prop :=
  ∀ (S T : Set ProfileGroup)
    (f : ProfileGroup ≃ ProfileGroup)
    (β : C3Cubed ≃+ C3Cubed),
    CayleyPresentationIso S T f →
    f (0 : ProfileGroup) = 0 →
    HasQuotientMap f β →
    (∀ a : C4, ∀ v : C3Cubed,
      (quotientCorrected f β (a, v)).2 = v) ∧
    (∀ a : C4, quotientCorrected f β (a, 0) = (a, 0))

/-- Claim 31475: in the conditional coprime fibre synchronization setting,
the original connection set is transported by the lifted quotient automorphism. -/
def claim31475 : Prop :=
  ∀ (S T : Set ProfileGroup)
    (f : ProfileGroup ≃ ProfileGroup)
    (β : C3Cubed ≃+ C3Cubed),
    InverseClosed S →
    InverseClosed T →
    CayleyPresentationIso S T f →
    f (0 : ProfileGroup) = 0 →
    HasQuotientMap f β →
    Set.image f S = Set.image (quotientLift β) S

end MathlibPlus.Open.CayleyProfiles.Batch
