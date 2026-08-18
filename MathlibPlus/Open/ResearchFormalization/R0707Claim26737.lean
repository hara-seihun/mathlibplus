import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0707Claim26737

noncomputable section

/-- The cover relation in the finite graded-poset carrier. -/
def coverRelation {P : Type*} [PartialOrder P] (x y : P) : Prop :=
  x < y ∧ ¬ ∃ z : P, x < z ∧ z < y

/-- A finite graded poset with its rank map and top rank. -/
def finiteGradedPoset {P : Type*} [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  (∀ v : P, rank v ≤ r) ∧
    (∀ x y : P, coverRelation x y → rank y = rank x + 1)

abbrev rankLevel {P : Type*} (rank : P → ℕ) (k : ℕ) :=
  {v : P // rank v = k}

noncomputable def rankSize {P : Type*} [Fintype P]
    (rank : P → ℕ) (k : ℕ) : ℕ :=
  letI := Fintype.ofFinite (rankLevel rank k)
  Fintype.card (rankLevel rank k)

noncomputable def raisingMatrix {P K : Type*} [Fintype P]
    [PartialOrder P] [Semiring K]
    (rank : P → ℕ) (w : P → P → K) : Matrix P P K :=
  letI := Classical.propDecidable
  fun x y => if coverRelation x y then w x y else 0

noncomputable def complementaryPowerMatrix {P K : Type*} [Fintype P]
    [PartialOrder P] [Semiring K]
    (r : ℕ) (rank : P → ℕ) (w : P → P → K) (k : ℕ) :
    Matrix (rankLevel rank k) (rankLevel rank (r - k)) K :=
  letI := Classical.decEq P
  fun x y => (raisingMatrix rank w ^ (r - 2 * k)) x.1 y.1

noncomputable def matrixAction {A B K : Type*} [Fintype A] [Semiring K]
    (M : Matrix A B K) (f : A → K) : B → K :=
  fun b => ∑ a : A, f a * M a b

/-- All strict complementary powers, including the odd-rank middle map. -/
def complementaryPowersFullRank {P K : Type*} [Fintype P]
    [PartialOrder P] [Field K]
    (r : ℕ) (rank : P → ℕ) (w : P → P → K) : Prop :=
  ∀ k : ℕ, 2 * k < r →
    Function.Bijective
      (matrixAction (complementaryPowerMatrix r rank w k))

def rankSymmetric {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : Fin (r + 1),
    rankSize rank k.val = rankSize rank (r - k.val)

def rankUnimodal {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : ℕ, 2 * k < r →
    rankSize rank k ≤ rankSize rank (k + 1)

def strictChain {P : Type*} [PartialOrder P]
    (k : ℕ) (s : Fin (k + 1) → P) : Prop :=
  ∀ ⦃i j : Fin (k + 1)⦄, i < j → s i < s j

def noChainOfLength {P : Type*} [PartialOrder P]
    (A : Set P) (k : ℕ) : Prop :=
  ∀ s : Fin (k + 1) → P,
    (∀ i, s i ∈ A) → ¬ strictChain k s

noncomputable def familyCard {P : Type*} [Fintype P] (A : Set P) : ℕ :=
  letI := Fintype.ofFinite {v : P // v ∈ A}
  Fintype.card {v : P // v ∈ A}

noncomputable def kLargestRankSum {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) (k : ℕ) : ℕ :=
  (Finset.univ : Finset (Finset (Fin (r + 1)))).sup
    (fun S =>
      if S.card = min k (r + 1) then
        ∑ j ∈ S, rankSize rank j.val
      else 0)

/-- The strong-Sperner condition: a family with no chain of length `k+1`
    has size at most the sum of the `k` largest rank sizes. -/
def strongSpernerProperty {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : ℕ, ∀ A : Set P,
    noChainOfLength A k → familyCard A ≤ kLargestRankSum r rank k

noncomputable def hasComplexCoverWeight {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℂ,
    (∀ x y, ¬ coverRelation x y → w x y = 0) ∧
      complementaryPowersFullRank r rank w

/-- Peckness consists of rank symmetry, rank unimodality, and the strong-Sperner
    property; it does not use the existence of a Lefschetz weighting. -/
def peckness {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  rankSymmetric r rank ∧
    rankUnimodal r rank ∧
      strongSpernerProperty r rank

noncomputable def hasStrictPositiveRealWeight {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℝ,
    (∀ x y, coverRelation x y → 0 < w x y) ∧
      (∀ x y, ¬ coverRelation x y → w x y = 0) ∧
        complementaryPowersFullRank r rank w

noncomputable def hasStrictPositiveRationalWeight {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℚ,
    (∀ x y, coverRelation x y → 0 < w x y) ∧
      (∀ x y, ¬ coverRelation x y → w x y = 0) ∧
        complementaryPowersFullRank r rank w

noncomputable def hasStrictPositiveIntegerWeight {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℤ,
    (∀ x y, coverRelation x y → 0 < w x y) ∧
      (∀ x y, ¬ coverRelation x y → w x y = 0) ∧
        complementaryPowersFullRank r rank
          (fun x y => (w x y : ℚ))

/-- Claim 26737: on every finite graded poset, Peckness is equivalent to the
    existence of complex, strictly positive real, strictly positive rational,
    and strictly positive integer cover weightings whose complementary powers
    are all invertible. -/
def claim26737_pecknessIffPositiveIntegerWeights : Prop :=
  ∀ (P : Type*) [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ),
    finiteGradedPoset r rank →
      (peckness r rank ↔ hasComplexCoverWeight r rank) ∧
        (hasComplexCoverWeight r rank ↔ hasStrictPositiveRealWeight r rank) ∧
          (hasStrictPositiveRealWeight r rank ↔
            hasStrictPositiveRationalWeight r rank) ∧
            (hasStrictPositiveRationalWeight r rank ↔
              hasStrictPositiveIntegerWeight r rank)

end

end MathlibPlus.Open.ResearchFormalization.R0707Claim26737
