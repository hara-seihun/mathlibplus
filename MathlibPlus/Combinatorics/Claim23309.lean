import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics.Claim23309

/-- The falling-factorial row for a card-type multiplicity map and a deck-count
map.  The map `a` records the multiset `S`, while `d` records the deck of the
host graph. -/
def fallingCubicRow {ι : Type*} [Fintype ι]
    (a d : ι → ℕ) : ℕ :=
  ∏ F, (d F).descFactorial (a F)

/-- Pointwise submultiset containment for multiplicity maps. -/
def containsCardSubmultiset {ι : Type*}
    (a d : ι → ℕ) : Prop :=
  ∀ F, a F ≤ d F

/-- Claim 23309: the falling cubic row is positive exactly when the deck
contains the three-card multiset.  The cubic condition is retained explicitly;
the source leaves the inessential permutation normalization unspecified. -/
def fallingCubicRowPos_iff_submultiset
    {ι : Type*} [Fintype ι]
    (a d : ι → ℕ) (_hcubic : ∑ F, a F = 3) : Prop :=
  0 < fallingCubicRow a d ↔ containsCardSubmultiset a d

end MathlibPlus.Combinatorics.Claim23309
