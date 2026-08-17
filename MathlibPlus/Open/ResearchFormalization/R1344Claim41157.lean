import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1344

noncomputable section

def affineMap41157 {p : ℕ} {H : Type*} [Group H]
    (multiplier : H → (ZMod p)ˣ) (τ : H → ZMod p) (σ : H ≃* H) :
    (ZMod p × H) → (ZMod p × H) :=
  fun x => ((multiplier x.2 : ZMod p) * x.1 + τ x.2, σ x.2)

def alphaMap41157 {p : ℕ} {H : Type*} [Group H]
    (β : H ≃* H) : (ZMod p × H) → (ZMod p × H) :=
  fun x => (-x.1, β x.2)

def identityLine41157 {p : ℕ} {H : Type*} [Group H] :
    Set (ZMod p × H) :=
  {x | x.2 = 1}

def identitySection41157 {p : ℕ} {H : Type*} [Group H]
    (S : Set (ZMod p × H)) : Set (ZMod p × H) :=
  S ∩ identityLine41157

def identityValues41157 {p : ℕ} {H : Type*} [Group H]
    (S : Set (ZMod p × H)) : Set (ZMod p) :=
  {a | (a, 1) ∈ S}

def inversePoint41157 {p : ℕ} {H : Type*} [Group H]
    (x : ZMod p × H) : ZMod p × H :=
  (-x.1, x.2⁻¹)

def inverseClosed41157 {p : ℕ} {H : Type*} [Group H]
    (S : Set (ZMod p × H)) : Prop :=
  ∀ x, x ∈ S → inversePoint41157 x ∈ S

def negationStable41157 {p : ℕ} {H : Type*} [Group H]
    (S : Set (ZMod p × H)) : Prop :=
  Set.image Neg.neg (identityValues41157 S) = identityValues41157 S

/-- Claim 41157: the normalized affine map fixes the identity section
pointwise, inverse closure makes that section negation-stable, and the
normalized affine map and the auxiliary alpha map have the same section image. -/
def claim41157 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ {H : Type*} [Group H]
      (multiplier : H → (ZMod p)ˣ) (τ : H → ZMod p)
      (σ β : H ≃* H) (S : Set (ZMod p × H)),
      multiplier 1 = 1 →
      τ 1 = 0 →
      inverseClosed41157 S →
      (∀ a : ZMod p,
        affineMap41157 multiplier τ σ (a, 1) = (a, 1)) ∧
      negationStable41157 S ∧
      Set.image (affineMap41157 multiplier τ σ) (identitySection41157 S) =
        Set.image (alphaMap41157 β) (identitySection41157 S)

end

end MathlibPlus.Open.ResearchFormalization.R1344
