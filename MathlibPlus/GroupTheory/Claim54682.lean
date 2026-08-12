import Mathlib

namespace MathlibPlus.GroupTheory.Claim54682

/-- Claim 54682: a subgroup of a product of finite groups of coprime orders
splits into its two coordinate intersections.  The displayed pointwise
form is equivalent to the subgroup equality in the source. -/
theorem subgroup_splits_of_coprime_orders
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (L : Subgroup (A × B)) :
    ∀ a b, (a, b) ∈ L ↔ (a, 1) ∈ L ∧ (1, b) ∈ L := by
  intro a b
  constructor
  · intro hab
    have hleft0 : (a ^ Nat.card B, 1) ∈ L := by
      have hpow := L.pow_mem hab (Nat.card B)
      simpa [Prod.pow_mk, pow_card_eq_one'] using hpow
    have hleft : (a, 1) ∈ L := by
      let k : ℤ := (Nat.card A).gcdB (Nat.card B)
      have hpow : ((a ^ Nat.card B) ^ k, (1 : B) ^ k) ∈ L :=
        L.zpow_mem hleft0 k
      have ha : (a ^ Nat.card B) ^ k = a :=
        (powCoprime hcop).left_inv a
      simpa [ha] using hpow
    have hright0 : (1, b ^ Nat.card A) ∈ L := by
      have hpow := L.pow_mem hab (Nat.card A)
      simpa [Prod.pow_mk, pow_card_eq_one'] using hpow
    have hright : (1, b) ∈ L := by
      let k : ℤ := (Nat.card B).gcdB (Nat.card A)
      have hpow : ((1 : A) ^ k, (b ^ Nat.card A) ^ k) ∈ L :=
        L.zpow_mem hright0 k
      have hb : (b ^ Nat.card A) ^ k = b :=
        (powCoprime hcop.symm).left_inv b
      simpa [hb] using hpow
    exact ⟨hleft, hright⟩
  · rintro ⟨hleft, hright⟩
    have hmul := L.mul_mem hleft hright
    simpa using hmul

end MathlibPlus.GroupTheory.Claim54682
