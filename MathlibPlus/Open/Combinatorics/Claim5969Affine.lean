import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Combinatorics.Claim5969

noncomputable section

/-- The proper nonempty, non-full subsets of the ordered root set. -/
def nonemptyProperSubset_claim5969 {r : ℕ}
    (T : Finset (Fin r)) : Prop :=
  T.Nonempty ∧ T ≠ (Finset.univ : Finset (Fin r))

/-- The alternating proper-margin contribution in the empty-cell formula. -/
def properMarginContribution_claim5969
    (r : ℕ) (m : Finset (Fin r) → ℤ) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin r))).filter
    (fun T => nonemptyProperSubset_claim5969 T),
    (-1 : ℤ) ^ (T.card + 1) * m T

/-- The empty-cell coordinate as an affine integer family in the full
intersection coordinate `t`, with the proper margins held fixed. -/
def emptyCellFamily_claim5969
    (r : ℕ) (q : ℤ) (m : Finset (Fin r) → ℤ) : ℤ → ℤ :=
  fun t => q - properMarginContribution_claim5969 r m + (-1 : ℤ) ^ r * t

/-- The exact fixed-proper-margin assertion: the affine family has at most one
parameter value whose empty cell is zero. -/
def affineEmptyCellOneParameter_claim5969 : Prop :=
  ∀ (r : ℕ) (q : ℤ) (m : Finset (Fin r) → ℤ),
    ∀ t₁ t₂ : ℤ,
      emptyCellFamily_claim5969 r q m t₁ = 0 →
      emptyCellFamily_claim5969 r q m t₂ = 0 →
      t₁ = t₂

end

end MathlibPlus.Open.Combinatorics.Claim5969
