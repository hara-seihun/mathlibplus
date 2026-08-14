import Mathlib

namespace MathlibPlus.Open.GroupTheory.AffineBatch

abbrev QuotientVertex := ZMod 28

/-- The regular shift `0 ↦ 1 ↦ ⋯ ↦ 27 ↦ 0`. -/
def regularShift : Equiv.Perm QuotientVertex where
  toFun := fun x => x + 1
  invFun := fun x => x - 1
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

abbrev RegularC28 :=
  Subgroup.closure ({regularShift} : Set (Equiv.Perm QuotientVertex))

/-- The conjugate-subgroup equality used for transporters.  This is the
standard convention `H ^ g = g⁻¹ H g`. -/
def ConjugatesRegularC28
    (c τ : Equiv.Perm QuotientVertex) : Prop :=
  ∀ x : Equiv.Perm QuotientVertex,
    c * x * c⁻¹ ∈ RegularC28 ↔
      τ * x * τ⁻¹ ∈ RegularC28

/-- Claim 31511: the normalizer coset exhausts all conjugators of the regular
`C₂₈` to its `τ`-conjugate. -/
def claim31511 : Prop :=
  (Nat.card (Subgroup.normalizer (RegularC28 : Set (Equiv.Perm QuotientVertex))) = 336) ∧
  ∀ τ : Equiv.Perm QuotientVertex,
    τ * τ = 1 →
    ∀ c : Equiv.Perm QuotientVertex,
      ConjugatesRegularC28 c τ →
      ∃ n : Subgroup.normalizer (RegularC28 : Set (Equiv.Perm QuotientVertex)),
        c = n.1 * τ

end MathlibPlus.Open.GroupTheory.AffineBatch
