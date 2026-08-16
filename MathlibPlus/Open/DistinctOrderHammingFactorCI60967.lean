import MathlibPlus.Open.CayleyCI.FormalizationBatch

namespace MathlibPlus.Open.FormalizationBatch

open MathlibPlus.Open.CayleyCI

/-- The ordered sum in a finite additive decomposition. -/
def orderedAddSum {A : Type*} [AddCommMonoid A] {k : ℕ}
    (x : Fin k → A) : A :=
  ∑ i, x i

/-- An internal direct sum of the displayed ordered additive subgroups. -/
def internalAddDirectSum {A : Type*} [AddCommGroup A] {k : ℕ}
    (H : Fin k → AddSubgroup A) : Prop :=
  ∀ a : A, ∃! x : Fin k → A,
    (∀ i : Fin k, x i ∈ H i) ∧ orderedAddSum x = a

/-- The punctured union of an ordered family of additive subgroups. -/
def addSubgroupPuncturedUnion {A : Type*} [AddGroup A] {k : ℕ}
    (H : Fin k → AddSubgroup A) : Set A :=
  {a | ∃ i : Fin k, a ∈ H i ∧ a ≠ 0}

/-- Claim 60967's generic distinct-order Hamming-factor theorem. -/
def distinctOrderHammingFactorTheorem : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A],
    ∀ k : ℕ, 3 ≤ k →
      ∀ H : Fin k → AddSubgroup A,
        internalAddDirectSum H →
        (∀ i : Fin k, ∃ a : A, a ∈ H i ∧ a ≠ 0) →
        Set.Pairwise (Set.univ : Set (Fin k))
          (fun i j => Nat.card (H i) ≠ Nat.card (H j)) →
        (∀ K : Fin k → AddSubgroup A,
          internalAddDirectSum K →
          (∀ i : Fin k, Nat.card (K i) = Nat.card (H i)) →
          ∃ α : A ≃+ A,
            ∀ i : Fin k, α '' (H i : Set A) = (K i : Set A)) →
        let S := addSubgroupPuncturedUnion H
        AddOrdinaryUndirectedCIConnectionSet A S ∧
          AddOrdinaryUndirectedCIConnectionSet A (AddIdentityFreeComplement S)

/-- A nonzero subspace of a finite coordinate vector space. -/
def nonzeroSubspace {p r : ℕ}
    (U : Submodule (ZMod p) (Fin r → ZMod p)) : Prop :=
  ∃ v : Fin r → ZMod p, v ∈ U ∧ v ≠ 0

/-- Internal direct sum for a displayed family of coordinate subspaces. -/
def internalSubspaceDirectSum {p r k : ℕ}
    (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)) : Prop :=
  ∀ v : Fin r → ZMod p, ∃! x : Fin k → (Fin r → ZMod p),
    (∀ i : Fin k, x i ∈ U i) ∧ ∑ i, x i = v

/-- The punctured union of a displayed family of coordinate subspaces. -/
def subspacePuncturedUnion {p r k : ℕ}
    (U : Fin k → Submodule (ZMod p) (Fin r → ZMod p)) :
    Set (Fin r → ZMod p) :=
  {v | ∃ i : Fin k, v ∈ U i ∧ v ≠ 0}

/-- The A4 consequence, including the maintained rank interval. -/
def ciElementaryAbelianOddResidualRanks : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], 5 ≤ p →
    ∀ r : ℕ, 6 ≤ r → r ≤ 2 * p + 2 →
      ∀ k : ℕ, 3 ≤ k →
        ∀ U : Fin k → Submodule (ZMod p) (Fin r → ZMod p),
          internalSubspaceDirectSum U →
          (∀ i : Fin k, nonzeroSubspace (U i)) →
          Set.Pairwise (Set.univ : Set (Fin k))
            (fun i j => Module.finrank (ZMod p) (U i) ≠
              Module.finrank (ZMod p) (U j)) →
          let S := subspacePuncturedUnion U
          AddOrdinaryUndirectedCIConnectionSet (Fin r → ZMod p) S ∧
            AddOrdinaryUndirectedCIConnectionSet
              (Fin r → ZMod p) (AddIdentityFreeComplement S)

/-- The explicit three-factor family retained under the A4 rank bound. -/
def ciElementaryAbelianOddResidualRanksUniformThreeFactor : Prop :=
  ∀ (p : ℕ) [Fact (Nat.Prime p)], 5 ≤ p →
    ∀ r : ℕ, 6 ≤ r → r ≤ 2 * p + 2 →
      ∃ U : Fin 3 → Submodule (ZMod p) (Fin r → ZMod p),
        internalSubspaceDirectSum U ∧
        (∀ i : Fin 3, nonzeroSubspace (U i)) ∧
        Module.finrank (ZMod p) (U 0) = 1 ∧
        Module.finrank (ZMod p) (U 1) = 2 ∧
        Module.finrank (ZMod p) (U 2) = r - 3 ∧
        let S := subspacePuncturedUnion U
        AddOrdinaryUndirectedCIConnectionSet (Fin r → ZMod p) S ∧
          AddOrdinaryUndirectedCIConnectionSet
            (Fin r → ZMod p) (AddIdentityFreeComplement S)

/-- The three-factor connection set in `F₂^r × C₉`. -/
def binaryC9HammingSet {r : ℕ}
    (U W : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Set ((Fin r → ZMod 2) × ZMod 9) :=
  {g | g.1 ∈ U ∧ g.1 ≠ 0 ∧ g.2 = 0} ∪
    {g | g.1 ∈ W ∧ g.1 ≠ 0 ∧ g.2 = 0} ∪
    {g | g.1 = 0 ∧ g.2 ≠ 0}

/-- The exact A6 complementary-pair hypothesis. -/
def binaryC9ComplementaryPair {r : ℕ}
    (U W : Submodule (ZMod 2) (Fin r → ZMod 2)) : Prop :=
  internalSubspaceDirectSum ![U, W] ∧
    nonzeroSubspace U ∧ nonzeroSubspace W ∧
    Module.finrank (ZMod 2) U ≠ Module.finrank (ZMod 2) W

/-- The A6 consequence for every maintained rank and every ordered pair of
nonzero unequal-dimensional binary summands. -/
def ciBinaryTimesC9Rank345 : Prop :=
  ∀ r : ℕ, (r = 3 ∨ r = 4 ∨ r = 5) →
    ∀ U W : Submodule (ZMod 2) (Fin r → ZMod 2),
      binaryC9ComplementaryPair U W →
      let S := binaryC9HammingSet U W
      AddOrdinaryUndirectedCIConnectionSet
          ((Fin r → ZMod 2) × ZMod 9) S ∧
        AddOrdinaryUndirectedCIConnectionSet
          ((Fin r → ZMod 2) × ZMod 9)
          (AddIdentityFreeComplement S)

/-- The unordered dimension alternatives listed for A6. -/
def binaryC9Rank345DimensionCase {r : ℕ}
    (U W : Submodule (ZMod 2) (Fin r → ZMod 2)) : Prop :=
  (r = 3 ∧
      ((Module.finrank (ZMod 2) U = 1 ∧ Module.finrank (ZMod 2) W = 2) ∨
        (Module.finrank (ZMod 2) U = 2 ∧ Module.finrank (ZMod 2) W = 1))) ∨
    (r = 4 ∧
      ((Module.finrank (ZMod 2) U = 1 ∧ Module.finrank (ZMod 2) W = 3) ∨
        (Module.finrank (ZMod 2) U = 3 ∧ Module.finrank (ZMod 2) W = 1))) ∨
    (r = 5 ∧
      ((Module.finrank (ZMod 2) U = 1 ∧ Module.finrank (ZMod 2) W = 4) ∨
        (Module.finrank (ZMod 2) U = 4 ∧ Module.finrank (ZMod 2) W = 1) ∨
        (Module.finrank (ZMod 2) U = 2 ∧ Module.finrank (ZMod 2) W = 3) ∨
        (Module.finrank (ZMod 2) U = 3 ∧ Module.finrank (ZMod 2) W = 2)))

/-- The rank/dimension labels made explicit by the A6 consequence. -/
def ciBinaryTimesC9Rank345DimensionCases : Prop :=
  ∀ r : ℕ, (r = 3 ∨ r = 4 ∨ r = 5) →
    ∀ U W : Submodule (ZMod 2) (Fin r → ZMod 2),
      binaryC9ComplementaryPair U W →
      binaryC9Rank345DimensionCase U W →
      let S := binaryC9HammingSet U W
      AddOrdinaryUndirectedCIConnectionSet
          ((Fin r → ZMod 2) × ZMod 9) S ∧
        AddOrdinaryUndirectedCIConnectionSet
          ((Fin r → ZMod 2) × ZMod 9)
          (AddIdentityFreeComplement S)

/-- Claim 60967, including the generic theorem and its A4/A6 consequences. -/
def distinctOrderHammingFactorCI_A4_A6 : Prop :=
  distinctOrderHammingFactorTheorem ∧
    ciElementaryAbelianOddResidualRanks ∧
    ciElementaryAbelianOddResidualRanksUniformThreeFactor ∧
    ciBinaryTimesC9Rank345 ∧
    ciBinaryTimesC9Rank345DimensionCases

end MathlibPlus.Open.FormalizationBatch
