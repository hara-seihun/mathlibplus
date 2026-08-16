import Mathlib

open scoped BigOperators Polynomial

namespace MathlibPlus.Open.ResearchFormalization.StableGaussianCounts14891

open Classical
noncomputable section

/-!
The source and target carriers below are the shifted level multisets from the
admitted stable-coloured construction.  A value in `Fin n` is the original
level minus one, so the source carrier has `r - 1` entries in levels
`0, ..., j` and the target carrier has `r` entries in levels `0, ..., j - 1`.
The carriers are genuine multisets: `finiteMultisets` enumerates their
multiplicity classes by finite words and removes the enumeration duplicates.
-/

/-- The shifted value of a level. -/
def shiftedLevel {n : ℕ} (i : Fin n) : ℕ := i.val

/-- The corresponding unshifted level, included to make the shift convention
explicit. -/
def originalLevel {n : ℕ} (i : Fin n) : ℕ := shiftedLevel i + 1

/-- All multisets of `k` elements from the finite level set `Fin n`. -/
def finiteMultisets (n k : ℕ) : Finset (Multiset (Fin n)) :=
  (Finset.univ : Finset (Fin k → Fin n)).image
    (fun f => Multiset.map f (Finset.univ : Finset (Fin k)).1)

/-- Shifted source multisets: `r - 1` entries from the `j + 1` levels. -/
def shiftedSourceMultisets (j r : ℕ) : Finset (Multiset (Fin (j + 1))) :=
  (finiteMultisets (j + 1) (r - 1)).filter (fun s => s.card = r - 1)

/-- Shifted target multisets: `r` entries from the `j` levels. -/
def shiftedTargetMultisets (j r : ℕ) : Finset (Multiset (Fin j)) :=
  (finiteMultisets j r).filter (fun s => s.card = r)

/-- Equal-weight means equal sum after the level shift. -/
def shiftedWeight {n : ℕ} (s : Multiset (Fin n)) : ℕ :=
  (s.map shiftedLevel).sum

/-- The number of source multisets in an equal shifted-weight fibre. -/
def shiftedSourceWeightCount (j r w : ℕ) : ℕ :=
  (shiftedSourceMultisets j r).filter (fun s => shiftedWeight s = w) |>.card

/-- The number of target multisets in an equal shifted-weight fibre. -/
def shiftedTargetWeightCount (j r w : ℕ) : ℕ :=
  (shiftedTargetMultisets j r).filter (fun s => shiftedWeight s = w) |>.card

/-- The source weight-generating polynomial. -/
def shiftedSourceGeneratingPolynomial (j r : ℕ) : Polynomial ℕ :=
  (shiftedSourceMultisets j r).sum
    (fun s => (Polynomial.X : Polynomial ℕ) ^ shiftedWeight s)

/-- The target weight-generating polynomial. -/
def shiftedTargetGeneratingPolynomial (j r : ℕ) : Polynomial ℕ :=
  (shiftedTargetMultisets j r).sum
    (fun s => (Polynomial.X : Polynomial ℕ) ^ shiftedWeight s)

/-- The Gaussian binomial polynomial, with the standard coefficient recurrence
for partitions in a rectangle. -/
def gaussianBinomialPolynomial : ℕ → ℕ → Polynomial ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
      gaussianBinomialPolynomial n k +
        (Polynomial.X : Polynomial ℕ) ^ (k + 1) *
          gaussianBinomialPolynomial n (k + 1)

/-- The actual top-layer source edge relation.  Its first clause is equal
factor weight, its second clause is the level-one condition, and its third
clause is dominance of the shifted-reversed partitions. -/
def stripStableTopEdge (j : ℕ)
    (source : Multiset (Fin (j + 1))) (target : Multiset (Fin j)) : Prop :=
  shiftedWeight source = shiftedWeight target ∧
    ((source.map shiftedLevel).count 0 ≤
      (target.map shiftedLevel).count 0) ∧
    (∀ k : ℕ,
      ((Multiset.sort (source.map shiftedLevel) (fun a b : ℕ => b ≤ a)).take k).sum ≥
        ((Multiset.sort (target.map shiftedLevel) (fun a b : ℕ => b ≤ a)).take k).sum)

/-- The cardinality of the neighbourhood of a set of top-layer sources. -/
def stripStableNeighbourhood (j : ℕ)
    (sources : Finset (Multiset (Fin (j + 1)))) : Finset (Multiset (Fin j)) :=
  (shiftedTargetMultisets j j).filter (fun target =>
    ∃ source ∈ sources, stripStableTopEdge j source target)

/-- Hall's condition for the exact strip-stable majorization graph. -/
def stripStableHallCondition (j : ℕ) : Prop :=
  ∀ sources : Finset (Multiset (Fin (j + 1))),
    sources ⊆ shiftedSourceMultisets j j →
      sources.card ≤ (stripStableNeighbourhood j sources).card

/-- The corresponding coefficient-count condition at the top layer. -/
def topCoefficientCountCondition (j : ℕ) : Prop :=
  (shiftedSourceMultisets j j).card ≤ (shiftedTargetMultisets j j).card

/-- A fixed finite relation showing that equal cardinalities alone do not
imply Hall's condition.  This is only the logical strictness witness; it is
not substituted for the strip-stable edge relation above. -/
def badHallRelation (a b : Fin 2) : Prop := b = 0

def badHallCondition : Prop :=
  ∀ sources : Finset (Fin 2),
    sources.card ≤
      ((Finset.univ : Finset (Fin 2)).filter (fun target =>
        ∃ source ∈ sources, badHallRelation source target)).card

def badHallStrictnessWitness : Prop :=
  (Finset.univ : Finset (Fin 2)).card ≤ (Finset.univ : Finset (Fin 2)).card ∧
    ¬ badHallCondition

/-- Hall implies the source-cardinality inequality for the actual top-layer
finite graph; the separate fixed witness records that this implication cannot
be reversed from cardinality data alone. -/
def hallIsStrictlyStrongerThanCardinality : Prop :=
  (∀ j : ℕ, 2 ≤ j →
    stripStableHallCondition j → topCoefficientCountCondition j) ∧
    badHallStrictnessWitness

/-- Butler's coefficientwise comparison in the stable range, stated directly
on the exact equal-weight fibres. -/
def coefficientwiseTargetDominatesSource (j r : ℕ) : Prop :=
  r < j → ∀ w : ℕ,
    shiftedSourceWeightCount j r w ≤ shiftedTargetWeightCount j r w

/-- The admitted Gaussian-binomial count statement and its exact Hall
bottleneck.  All quantifiers are over the shifted multiset carriers above;
no generic carrier or unconstrained certificate is used. -/
def claim14891 : Prop :=
  (∀ j r : ℕ, 1 ≤ r → r ≤ j →
    shiftedSourceGeneratingPolynomial j r =
      gaussianBinomialPolynomial (j + r - 1) (r - 1) ∧
    shiftedTargetGeneratingPolynomial j r =
      gaussianBinomialPolynomial (j + r - 1) r ∧
    (∀ w : ℕ,
      shiftedSourceWeightCount j r w =
        (gaussianBinomialPolynomial (j + r - 1) (r - 1)).coeff w) ∧
    (∀ w : ℕ,
      shiftedTargetWeightCount j r w =
        (gaussianBinomialPolynomial (j + r - 1) r).coeff w)) ∧
  (∀ j r : ℕ, 1 ≤ r → r ≤ j →
    coefficientwiseTargetDominatesSource j r) ∧
  (∀ j r : ℕ, 1 ≤ r → r ≤ j → r = j →
    (∀ w : ℕ,
      shiftedSourceWeightCount j r w = shiftedTargetWeightCount j r w) ∧
      shiftedSourceGeneratingPolynomial j r = shiftedTargetGeneratingPolynomial j r) ∧
  hallIsStrictlyStrongerThanCardinality

end
end MathlibPlus.Open.ResearchFormalization.StableGaussianCounts14891
