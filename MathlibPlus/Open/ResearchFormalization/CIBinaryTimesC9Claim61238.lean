import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61238

noncomputable section

abbrev BinaryBase (r : ℕ) := Fin r → ZMod 2
abbrev BinaryNine (r : ℕ) := BinaryBase r × ZMod 9

/-- Identity-free connection sets on the additive group. -/
def identityFreeSet {r : ℕ} (S : Set (BinaryNine r)) : Prop :=
  (0 : BinaryNine r) ∉ S

/-- Inverse closure on the additive group. -/
def inverseClosedSet {r : ℕ} (S : Set (BinaryNine r)) : Prop :=
  ∀ ⦃x : BinaryNine r⦄, x ∈ S → -x ∈ S

/-- The ordinary additive Cayley adjacency relation on `F₂^r × C₉`. -/
def binaryC9CayleyAdjacency {r : ℕ}
    (S : Set (BinaryNine r))
    (x y : BinaryNine r) : Prop :=
  x ≠ y ∧ y - x ∈ S

/-- A pointed graph isomorphism for the displayed Cayley relations. -/
def binaryC9GraphIsomorphism {r : ℕ}
    (S T : Set (BinaryNine r))
    (f : BinaryNine r ≃ BinaryNine r) : Prop :=
  ∀ x y : BinaryNine r,
    binaryC9CayleyAdjacency S x y ↔
      binaryC9CayleyAdjacency T (f x) (f y)

/-- The exact fibre-preserving form with a group-linear binary quotient map. -/
def fibrewiseLinearForm {r : ℕ}
    (f : BinaryNine r ≃ BinaryNine r)
    (L : BinaryBase r ≃ₗ[ZMod 2] BinaryBase r)
    (σ : BinaryBase r → Equiv.Perm (ZMod 9)) : Prop :=
  ∀ (x : BinaryBase r) (z : ZMod 9),
    f (x, z) = (L x, σ x z)

/-- Claim 61238: in ranks `3, 4, 5`, an identity-free inverse-closed
connection-set pair with a pointed fibre-preserving Cayley isomorphism whose
binary quotient is linear has a group-automorphism transporter. -/
def claim61238 : Prop :=
  ∀ (r : ℕ),
    (r = 3 ∨ r = 4 ∨ r = 5) →
    ∀ (S T : Set (BinaryNine r)),
      identityFreeSet S →
      identityFreeSet T →
      inverseClosedSet S →
      inverseClosedSet T →
      ∀ (f : BinaryNine r ≃ BinaryNine r),
        f 0 = 0 →
        ∀ (L : BinaryBase r ≃ₗ[ZMod 2] BinaryBase r)
          (σ : BinaryBase r → Equiv.Perm (ZMod 9)),
          fibrewiseLinearForm f L σ →
          binaryC9GraphIsomorphism S T f →
          ∃ α : BinaryNine r ≃+ BinaryNine r,
            α '' S = T

end
end MathlibPlus.Open.ResearchFormalization.CIBinaryTimesC9Claim61238
