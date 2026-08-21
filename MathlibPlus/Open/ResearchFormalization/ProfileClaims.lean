import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ProfileClaims

universe u v

/-- The fiber map in the normalized relative derivative formula. -/
def profileFiberDerivative {B : Type u} {H : Type v} [AddGroup B] [Group H]
    (p : H → Equiv.Perm B) (a : H) (u : B) (h : H) : Equiv.Perm B :=
  (p h)⁻¹ * Equiv.addRight (-(p a u)) * p (h * a) * Equiv.addRight u

/-- The derivative acts fiberwise and fixes the `H` coordinate. -/
def normalizedRelativeDerivative {B : Type u} {H : Type v} [AddGroup B] [Group H]
    (p : H → Equiv.Perm B) (a : H) (u : B) : Equiv.Perm (B × H) :=
  Equiv.prodCongrLeft (fun h => profileFiberDerivative p a u h)

/-- The identity-base fiber profile. -/
def identityBaseProfile {B : Type u} {H : Type v}
    (p : H → Equiv.Perm B) : Equiv.Perm (B × H) :=
  Equiv.prodCongrLeft p

def derivativeInvariant {B : Type u} {H : Type v} [AddGroup B] [Group H]
    (p : H → Equiv.Perm B) (S : Set (B × H)) : Prop :=
  ∀ (a : H) (u : B), Set.image (normalizedRelativeDerivative p a u) S = S

def derivativeGroup {B : Type u} {H : Type v} [AddGroup B] [Group H]
    (p : H → Equiv.Perm B) : Subgroup (Equiv.Perm (B × H)) :=
  Subgroup.closure
    (Set.range (fun au : H × B => normalizedRelativeDerivative p au.1 au.2))

def derivativeOrbit {B : Type u} {H : Type v} [AddGroup B] [Group H]
    (p : H → Equiv.Perm B) (x : B × H) : Set (B × H) :=
  {y | ∃ g : Equiv.Perm (B × H), g ∈ derivativeGroup p ∧ g x = y}

def fiberSection {B : Type u} {H : Type v}
    (S : Set (B × H)) (a : H) : Set B :=
  {x | (x, a) ∈ S}

def translateSet {B : Type u} [Add B] (X : Set B) (t : B) : Set B :=
  {x | ∃ y ∈ X, x = y + t}

def imageSet {B : Type u} (p : Equiv.Perm B) (X : Set B) : Set B :=
  Set.image p X

def claim_38769 : Prop := by
  classical
  exact ∀ {B : Type u} {H : Type v} [AddCommGroup B] [Group H]
    (p : H → Equiv.Perm B), p 1 = Equiv.refl B →
    ∀ (S : Set (B × H)) (a : H), derivativeInvariant p S →
    let X := fiberSection S a
    (∀ (t : B) (k : H),
      imageSet (p (a * k)) (translateSet X t) =
        translateSet (imageSet (p a) X) (p k t)) ∧
    (∀ (t : B),
      imageSet (p a) (translateSet X t) =
        translateSet (imageSet (p a) X) t) ∧
    imageSet (p a) X = translateSet X (-(p (a⁻¹) 0))

def claim_38773 : Prop := by
  classical
  exact ∀ {B : Type u} {H : Type v} [AddCommGroup B] [Group H]
    [Fintype B] [Fintype H],
    Nat.Coprime (Fintype.card B) (Fintype.card H) →
    ∀ (p : H → Equiv.Perm B), p 1 = Equiv.refl B →
      ∀ x : B × H,
        Set.image (identityBaseProfile p) (derivativeOrbit p x) =
          derivativeOrbit p x

abbrev C3 := Multiplicative (ZMod 3)

def c3Profile : C3 → Equiv.Perm (ZMod 3) :=
  fun h => Equiv.addRight (Multiplicative.toAdd h)

def c3Shear : (ZMod 3 × ZMod 3) ≃+ (ZMod 3 × ZMod 3) :=
  { toFun := fun x => (x.1 + x.2, x.2)
    invFun := fun x => (x.1 - x.2, x.2)
    left_inv := by
      intro x
      ext <;> simp [sub_eq_add_neg, add_assoc]
    right_inv := by
      intro x
      ext <;> simp [sub_eq_add_neg, add_left_comm, add_comm]
    map_add' := by
      intro x y
      ext <;> simp [add_left_comm, add_comm] }

def claim_38775 : Prop := by
  classical
  let f := identityBaseProfile c3Profile
  exact
    c3Profile 1 = Equiv.refl (ZMod 3) ∧
    (∀ (x : ZMod 3) (h : C3),
      f (x, h) = (x + Multiplicative.toAdd h, h)) ∧
    c3Shear.toMultiplicative ≠ MulEquiv.refl (Multiplicative (ZMod 3 × ZMod 3)) ∧
    (∀ (a : C3) (u : ZMod 3), normalizedRelativeDerivative c3Profile a u = 1) ∧
    (∀ x : ZMod 3 × C3, derivativeOrbit c3Profile x = {x}) ∧
    Fintype.card {x : ZMod 3 × C3 //
      derivativeOrbit c3Profile x = {x} ∧ f x ≠ x} = 6

abbrev C2Cubed := Fin 3 → ZMod 2
abbrev C9 := Multiplicative (ZMod 9)

def claim_38785 : Prop := by
  classical
  exact ∀ (p : C9 → Equiv.Perm C2Cubed), p 1 = Equiv.refl C2Cubed →
    ∀ S : Set (C2Cubed × C9), derivativeInvariant p S →
      Set.image (identityBaseProfile p) S = S

end MathlibPlus.Open.ResearchFormalization.ProfileClaims
