import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0707Claim26743

private def isCover {P : Type*} [PartialOrder P] (x y : P) : Prop :=
  x < y ∧ ¬ ∃ z : P, x < z ∧ z < y

private def isFiniteGradedPoset {P : Type*} [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  (∀ v : P, rank v ≤ r) ∧
    (∀ x y : P, isCover x y → rank y = rank x + 1)

private abbrev rankLevel {P : Type*} (rank : P → ℕ) (k : ℕ) :=
  {v : P // rank v = k}

private noncomputable def rankSize {P : Type*} [Fintype P]
    (rank : P → ℕ) (k : ℕ) : ℕ := by
  classical
  letI := Fintype.ofFinite (rankLevel rank k)
  exact Fintype.card (rankLevel rank k)

private noncomputable def raisingMatrix {P K : Type*} [Fintype P]
    [PartialOrder P] [Semiring K]
    (rank : P → ℕ) (w : P → P → K) : Matrix P P K := by
  classical
  exact fun x y => if isCover x y then w x y else 0

private noncomputable def complementaryPowerMatrix {P K : Type*} [Fintype P]
    [PartialOrder P] [Semiring K]
    (r : ℕ) (rank : P → ℕ) (w : P → P → K) (k : ℕ) :
    Matrix (rankLevel rank k) (rankLevel rank (r - k)) K := by
  classical
  exact fun x y =>
    (raisingMatrix rank w ^ (r - 2 * k)) x.1 y.1

private noncomputable def matrixAction {A B K : Type*} [Fintype A] [Semiring K]
    (M : Matrix A B K) (f : A → K) : B → K := by
  classical
  exact fun b => ∑ a : A, f a * M a b

private def complementaryPowerFullRank {P K : Type*} [Fintype P]
    [PartialOrder P] [Field K]
    (r : ℕ) (rank : P → ℕ) (w : P → P → K) : Prop :=
  ∀ k : ℕ, 2 * k ≤ r →
    Function.Bijective
      (matrixAction (complementaryPowerMatrix r rank w k))

private def rankSymmetric {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : Fin (r + 1),
    rankSize rank k.val = rankSize rank (r - k.val)

private def rankUnimodal {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : ℕ, 2 * k < r →
    rankSize rank k ≤ rankSize rank (k + 1)

private noncomputable def kLargestRankSum {P : Type*} [Fintype P]
    (r : ℕ) (rank : P → ℕ) (k : ℕ) : ℕ := by
  classical
  exact
    (Finset.univ : Finset (Finset (Fin (r + 1)))).sup
      (fun S =>
        if S.card = min k (r + 1) then
          ∑ j ∈ S, rankSize rank j.val
        else 0)

private def strictChain {P : Type*} [PartialOrder P]
    (k : ℕ) (s : Fin (k + 1) → P) : Prop :=
  ∀ ⦃i j : Fin (k + 1)⦄, i < j → s i < s j

private def noChainOfLength {P : Type*} [PartialOrder P]
    (A : Set P) (k : ℕ) : Prop :=
  ∀ s : Fin (k + 1) → P,
    (∀ i, s i ∈ A) → ¬ strictChain k s

private noncomputable def familyCard {P : Type*} [Fintype P] (A : Set P) : ℕ := by
  classical
  letI := Fintype.ofFinite {v : P // v ∈ A}
  exact Fintype.card {v : P // v ∈ A}

private def strongSpernerProperty {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∀ k : ℕ, ∀ A : Set P,
    noChainOfLength A k →
      familyCard A ≤ kLargestRankSum r rank k

private def isSymmetricChain {P : Type*} [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (C : Set P) : Prop :=
  C.Nonempty ∧
    (∀ x ∈ C, ∀ y ∈ C, x = y ∨ x < y ∨ y < x) ∧
    (∃ a ∈ C, ∃ b ∈ C,
      (∀ x ∈ C, rank a ≤ rank x ∧ rank x ≤ rank b) ∧
      rank a + rank b = r ∧
      (∀ k : ℕ, rank a ≤ k → k ≤ rank b →
        ∃! x, x ∈ C ∧ rank x = k) ∧
      (∀ x ∈ C, ∀ y ∈ C, rank y = rank x + 1 → isCover x y))

private def symmetricChainDecomposition {P : Type*} [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (𝒞 : Set (Set P)) : Prop :=
  𝒞.Finite ∧
    (∀ C, C ∈ 𝒞 → isSymmetricChain r rank C) ∧
    (∀ v : P, ∃! C, C ∈ 𝒞 ∧ v ∈ C)

private def selectedChainCover {P : Type*} [PartialOrder P]
    (𝒞 : Set (Set P)) (x y : P) : Prop :=
  ∃ C, C ∈ 𝒞 ∧ x ∈ C ∧ y ∈ C ∧ isCover x y

private noncomputable def chainCoverWeight {P : Type*} [PartialOrder P]
    (𝒞 : Set (Set P)) : P → P → ℚ := by
  classical
  exact fun x y => if selectedChainCover 𝒞 x y then 1 else 0

private def chainComplementaryPowerIsPermutation
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) (𝒞 : Set (Set P))
    (w : P → P → ℚ) : Prop :=
  ∀ k : ℕ, 2 * k ≤ r →
    ∃ π : rankLevel rank k ≃ rankLevel rank (r - k),
      (∀ x, ∃ C, C ∈ 𝒞 ∧ x.1 ∈ C ∧ (π x).1 ∈ C) ∧
      ∀ x y,
        (π x = y ∧
            (complementaryPowerMatrix r rank w k) x y = 1) ∨
          (π x ≠ y ∧
            (complementaryPowerMatrix r rank w k) x y = 0)

private def hasComplexLefschetzWeight {P : Type*} [Fintype P]
    [PartialOrder P] (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℂ,
    (∀ x y, ¬ isCover x y → w x y = 0) ∧
      complementaryPowerFullRank r rank w

private def peckPoset {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  rankSymmetric r rank ∧
    rankUnimodal r rank ∧
      hasComplexLefschetzWeight r rank

private def strictPositiveIntegerLefschetzWeight
    {P : Type*} [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ) : Prop :=
  ∃ w : P → P → ℤ,
    (∀ x y, isCover x y → 0 < w x y) ∧
      (∀ x y, ¬ isCover x y → w x y = 0) ∧
        complementaryPowerFullRank r rank
          (fun x y => (w x y : ℚ))

/-- Claim 26743: an SCD, with its chains oriented upward and its selected
    covers weighted by one, gives the complementary permutation matrices.
    It therefore gives the exact Peck rank shape and all no-`(k+1)`-chain
    strong-Sperner bounds, and the positive-integer characterization supplies
    a strictly positive integer Lefschetz weighting. -/
def claim26743_symmetricChainsGiveZeroOneLefschetz : Prop :=
  ∀ (P : Type*) [Fintype P] [PartialOrder P]
    (r : ℕ) (rank : P → ℕ),
    isFiniteGradedPoset r rank →
      ∀ 𝒞 : Set (Set P),
        symmetricChainDecomposition r rank 𝒞 →
          chainComplementaryPowerIsPermutation r rank 𝒞
              (chainCoverWeight 𝒞) ∧
            peckPoset r rank ∧
              strongSpernerProperty r rank ∧
                strictPositiveIntegerLefschetzWeight r rank

end MathlibPlus.Open.ResearchFormalization.R0707Claim26743
