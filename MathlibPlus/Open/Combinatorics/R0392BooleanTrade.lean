import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

/-- The complete outside-neighborhood table on the Boolean trace cells. -/
abbrev BooleanTable (r : ℕ) := Finset (Fin r) → ℕ

/-- The signed cell space used for kernel directions. -/
abbrev SignedBooleanTable (r : ℕ) := Finset (Fin r) → ℤ

/-- All exact trace cells indexed by subsets of the ordered root set. -/
def booleanCells (r : ℕ) : Finset (Finset (Fin r)) :=
  Finset.univ

/-- Total outside mass of a signed table. -/
def signedTotal {r : ℕ} (x : SignedBooleanTable r) : ℤ :=
  ∑ S : Finset (Fin r), x S

/-- Total outside mass of a nonnegative table. -/
def naturalTotal {r : ℕ} (x : BooleanTable r) : ℕ :=
  ∑ S : Finset (Fin r), x S

/-- The common-neighborhood margin indexed by a root subset. -/
def signedMargin {r : ℕ} (x : SignedBooleanTable r)
    (T : Finset (Fin r)) : ℤ :=
  Finset.sum ((booleanCells r).filter (fun S => T ⊆ S)) (fun S => x S)

/-- The natural-valued margin of a nonnegative table. -/
def naturalMargin {r : ℕ} (x : BooleanTable r)
    (T : Finset (Fin r)) : ℕ :=
  Finset.sum ((booleanCells r).filter (fun S => T ⊆ S)) (fun S => x S)

/-- The nonempty proper subsets of the ordered root set. -/
def nonemptyProperCell {r : ℕ} (T : Finset (Fin r)) : Prop :=
  T.Nonempty ∧ T ≠ (Finset.univ : Finset (Fin r))

/-- The alternating Boolean trade on the complete cell table. -/
def primitiveTrade {r : ℕ} (S : Finset (Fin r)) : ℤ :=
  (-1 : ℤ) ^ (r - S.card)

/-- The signed directions preserving total mass and every nonempty proper
margin. -/
def properMarginKernel {r : ℕ} (x : SignedBooleanTable r) : Prop :=
  signedTotal x = 0 ∧
    ∀ T : Finset (Fin r), nonemptyProperCell T → signedMargin x T = 0

/-- The proper-margin kernel is the one-dimensional alternating Boolean trade. -/
def claim_20833 : Prop :=
  ∀ r : ℕ, ∀ x : SignedBooleanTable r,
    properMarginKernel x ↔
      ∃ c : ℤ, ∀ S : Finset (Fin r),
        x S = c * primitiveTrade S

/-- The positive and negative unit-cell supports of the primitive trade. -/
def positiveTradeCells (r : ℕ) : Finset (Finset (Fin r)) :=
  (booleanCells r).filter (fun S => primitiveTrade S = 1)

def negativeTradeCells (r : ℕ) : Finset (Finset (Fin r)) :=
  (booleanCells r).filter (fun S => primitiveTrade S = -1)

/-- The first nontrivial nonnegative ambiguity in a proper-margin fiber has
outside order at least the mass of one sign of the primitive trade. -/
def claim_20834 : Prop :=
  ∀ r : ℕ,
    (positiveTradeCells r).card = 2 ^ (r - 1) ∧
      (negativeTradeCells r).card = 2 ^ (r - 1) ∧
      ∀ x y : BooleanTable r,
        x ≠ y →
          naturalTotal x = naturalTotal y →
            (∀ T : Finset (Fin r), nonemptyProperCell T →
              naturalMargin x T = naturalMargin y T) →
              2 ^ (r - 1) ≤ naturalTotal x

end

end MathlibPlus.Open.Combinatorics.R0392
