import Mathlib

namespace MathlibPlus.Combinatorics

/-!
Finite saturation core of admitted claim 56907.  The `P`-fibre is represented by
`F`, and the selected basic-set intersection by `A`.
-/

/-- A subset of a `p`-element fibre whose cardinality is divisible by `p` is
empty or is the whole fibre. -/
theorem fibre_subset_empty_or_eq_of_card_dvd_claim56907
    {α : Type*} [DecidableEq α] {F A : Finset α} {p : ℕ}
    (hF : F.card = p) (hA : A ⊆ F) (hp : p ∣ A.card) :
    A = ∅ ∨ A = F := by
  by_cases hzero : A.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · right
    have hle : A.card ≤ F.card := Finset.card_le_card hA
    have hpos : 0 < A.card := Nat.pos_of_ne_zero hzero
    have hp_le : p ≤ A.card := Nat.le_of_dvd hpos hp
    have hcard : A.card = F.card := by omega
    exact Finset.eq_of_subset_of_card_le hA (by omega)

end MathlibPlus.Combinatorics
