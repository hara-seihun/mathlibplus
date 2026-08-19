import Mathlib.Combinatorics.Young.YoungDiagram

namespace MathlibPlus.Combinatorics.Claim59179

/-- The `α` carrier: weakly decreasing positive row lengths, bounded by `j`,
with the empty list representing the empty partition. -/
def carrierA (j n : ℕ) : Set (List ℕ) :=
  {α | α.SortedGE ∧ (∀ a ∈ α, 0 < a) ∧
    (∀ a ∈ α, a ≤ j) ∧ α.length ≤ n - 1}

/-- The adjacent target carrier with width at most `j-1` and length at most
`n`. -/
def carrierT (j n : ℕ) : Set (List ℕ) :=
  {μ | μ.SortedGE ∧ (∀ m ∈ μ, 0 < m) ∧
    (∀ m ∈ μ, m ≤ j - 1) ∧ μ.length ≤ n}

/-- Cells of the skew diagram `(j, α)/(j-1)`. -/
def skewCells (j : ℕ) (α : List ℕ) : Finset (ℕ × ℕ) :=
  YoungDiagram.cellsOfRowLens (j :: α) \
    YoungDiagram.cellsOfRowLens [j - 1]

/-- The exact skew-cell cardinality statement, with no proof hidden in the
formalization. -/
def skewCells_card : Prop :=
  ∀ (j : ℕ) (α : List ℕ), 1 ≤ j →
    (skewCells j α).card = α.sum + 1

/-- Claim 59179: under `j≥2` and `1≤n<j`, every `α` in the exact adjacent
carrier has skew diagram size `|α|+1`; the companion `μ` carrier remains an
explicit part of the setting. -/
def adjacentCarrierDomainsAndSkewDiagram_claim59179 : Prop :=
  ∀ (j n : ℕ), 2 ≤ j → 1 ≤ n → n < j →
    ∀ α : List ℕ, α ∈ carrierA j n →
      (skewCells j α).card = α.sum + 1

end MathlibPlus.Combinatorics.Claim59179
