import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1346

noncomputable section

/-- The image of a subset under an element of a group action. -/
def actionImage {G Ω : Type*} [Group G] [MulAction G Ω]
    (g : G) (S : Set Ω) : Set Ω :=
  {y | ∃ x, x ∈ S ∧ g • x = y}

/-- Transitivity of the ambient action. -/
def transitiveAction {G Ω : Type*} [Group G] [MulAction G Ω] : Prop :=
  ∀ x y : Ω, ∃ g : G, g • x = y

/-- A partition of a carrier by nonempty, disjoint cells. -/
def partitionOf {Ω : Type*} (P : Set (Set Ω)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧
    (∀ x : Ω, ∃ C, C ∈ P ∧ x ∈ C) ∧
      (∀ C D, C ∈ P → D ∈ P → C ≠ D → Disjoint C D)

/-- A partition of the subset `B0`; its cells are not required to cover the
complement of `B0`. -/
def partitionOfSubset {Ω : Type*}
    (B0 : Set Ω) (P : Set (Set Ω)) : Prop :=
  (∀ C ∈ P, C.Nonempty) ∧
    (∀ x : Ω, x ∈ B0 → ∃ C, C ∈ P ∧ x ∈ C) ∧
      (∀ C D, C ∈ P → D ∈ P → C ≠ D → Disjoint C D) ∧
        (∀ C ∈ P, C ⊆ B0)

/-- A group preserves a partition setwise. -/
def invariantPartition {G Ω : Type*} [Group G] [MulAction G Ω]
    (P : Set (Set Ω)) : Prop :=
  ∀ g : G, ∀ C ∈ P, actionImage g C ∈ P

/-- The outer partition and its `G`-invariance. -/
def outerPartition {G Ω : Type*} [Group G] [MulAction G Ω]
    (B : Set (Set Ω)) : Prop :=
  partitionOf B ∧ invariantPartition (G := G) (Ω := Ω) B

/-- Refinement of one partition by another. -/
def refines {Ω : Type*}
    (Q B : Set (Set Ω)) : Prop :=
  ∀ C ∈ Q, ∃ D ∈ B, C ⊆ D

/-- Equality of the restriction of a global family to the base block. -/
def restrictsTo {Ω : Type*}
    (Q Q0 : Set (Set Ω)) (B0 : Set Ω) : Prop :=
  (∀ C ∈ Q0, C ∈ Q) ∧
    (∀ C ∈ Q, C ⊆ B0 → C ∈ Q0)

/-- A local block system is a partition of `B0`, invariant under the full
setwise stabilizer of `B0` in `G`. -/
def localBlockSystem {G Ω : Type*} [Group G] [MulAction G Ω]
    (B0 : Set Ω) (Q0 : Set (Set Ω)) : Prop :=
  partitionOfSubset B0 Q0 ∧
    ∀ g : G, actionImage g B0 = B0 →
      ∀ C ∈ Q0, actionImage g C ∈ Q0

/-- Nontriviality for a partition of the carrier `B0`. -/
def nontrivialLocalPartition {Ω : Type*}
    (B0 : Set Ω) (Q0 : Set (Set Ω)) : Prop :=
  Q0 ≠ ({B0} : Set (Set Ω)) ∧
    ¬(∀ C ∈ Q0, ∀ x ∈ C, ∀ y ∈ C, x = y)

/-- The transported local family along `g`. -/
def transportedLocalSystem {G Ω : Type*} [Group G] [MulAction G Ω]
    (Q0 : Set (Set Ω)) (g : G) : Set (Set Ω) :=
  {C | ∃ C0, C0 ∈ Q0 ∧ C = actionImage g C0}

/-- The union of transported local families over the outer blocks. -/
def transportedPartition {G Ω : Type*} [Group G] [MulAction G Ω]
    (B : Set (Set Ω)) (B0 : Set Ω) (Q0 : Set (Set Ω)) : Set (Set Ω) :=
  {C | ∃ D, D ∈ B ∧ ∃ g : G,
    actionImage g B0 = D ∧ C ∈ transportedLocalSystem Q0 g}

/-- Independence of the representative transporting `B0` to `D`. -/
def transportIndependent {G Ω : Type*} [Group G] [MulAction G Ω]
    (B0 : Set Ω) (Q0 : Set (Set Ω)) (D : Set Ω) : Prop :=
  ∀ g h : G,
    actionImage g B0 = D → actionImage h B0 = D →
      transportedLocalSystem Q0 g = transportedLocalSystem Q0 h

/-- The full canonical conclusion for the transported refinement. -/
def canonicalTransportedRefinement
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (B : Set (Set Ω)) (B0 : Set Ω) (Q0 : Set (Set Ω)) : Prop :=
  (∀ D ∈ B, transportIndependent (G := G) (Ω := Ω) B0 Q0 D) ∧
    let Q := transportedPartition (G := G) (Ω := Ω) B B0 Q0
    partitionOf Q ∧
      invariantPartition (G := G) (Ω := Ω) Q ∧
        refines Q B ∧ restrictsTo Q Q0 B0

/-- All cells of the outer partition have the stated finite size. -/
def outerBlocksHaveSize {Ω : Type*}
    (B : Set (Set Ω)) (n : ℕ) : Prop :=
  ∀ D ∈ B, Nat.card {x : Ω // x ∈ D} = n

/-- A cyclic subgroup of order `p*q` in the kernel of the outer block
action, regular on every outer block. -/
def cyclicRegularOuterKernel {G Ω : Type*} [Group G] [MulAction G Ω]
    (B : Set (Set Ω)) (C : Subgroup G) (p q : ℕ) : Prop :=
  Nat.card C = p * q ∧
    IsCyclic C ∧
      (∀ c : C, ∀ D ∈ B, actionImage (c : G) D = D) ∧
        (∀ D ∈ B, ∀ x y : Ω, x ∈ D → y ∈ D →
          ∃! c : C, (c : G) • x = y)

/-- A characteristic subgroup of order `r` inside `C`. -/
def characteristicSubgroupWithin {G : Type*} [Group G]
    (C K : Subgroup G) (r : ℕ) : Prop :=
  K ≤ C ∧ Nat.card K = r ∧
    ∀ φ : C ≃* C, ∀ k : C,
      ((k : G) ∈ K ↔ (φ k : G) ∈ K)

/-- There is exactly one characteristic subgroup of the stated order. -/
def uniqueCharacteristicSubgroup {G : Type*} [Group G]
    (C : Subgroup G) (r : ℕ) : Prop :=
  ∃! K : Subgroup G, characteristicSubgroupWithin C K r

/-- The orbit partition of a subgroup acting on `Ω`. -/
def orbitPartition {G Ω : Type*} [Group G] [MulAction G Ω]
    (K : Subgroup G) : Set (Set Ω) :=
  {C | ∃ x : Ω, C = {y | ∃ k : K, (k : G) • x = y}}

/-- Claim 41176: the transported local partitions are representative-independent
and form the canonical invariant global refinement. -/
def claim41176_canonicalTransportedPartition : Prop :=
  ∀ (G Ω : Type*) [Group G] [MulAction G Ω]
    (B : Set (Set Ω)) (B0 : Set Ω) (Q0 : Set (Set Ω)),
    transitiveAction (G := G) (Ω := Ω) →
      outerPartition (G := G) (Ω := Ω) B →
        B0 ∈ B →
          localBlockSystem (G := G) (Ω := Ω) B0 Q0 →
            canonicalTransportedRefinement
              (G := G) (Ω := Ω) B B0 Q0

/-- The cell-size predicate used for the global refinement. -/
def cellSize {Ω : Type*}
    (Q : Set (Set Ω)) (r : ℕ) : Prop :=
  ∀ C ∈ Q, Nat.card {x : Ω // x ∈ C} = r

/-- Claim 41178: a nontrivial local block system has prime cell size, and
its canonical global refinement is literally the orbit partition of the
corresponding characteristic subgroup in each marked cycle. -/
def claim41178_literalCharacteristicOrbitRefinement : Prop :=
  ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q →
    ∀ (G Ω : Type*) [Group G] [MulAction G Ω]
      (B : Set (Set Ω)) (B0 : Set Ω) (Q0 : Set (Set Ω))
      (C D : Subgroup G),
      transitiveAction (G := G) (Ω := Ω) →
        outerPartition (G := G) (Ω := Ω) B →
          outerBlocksHaveSize B (p * q) →
            B0 ∈ B →
              localBlockSystem (G := G) (Ω := Ω) B0 Q0 →
                nontrivialLocalPartition B0 Q0 →
                  cyclicRegularOuterKernel B C p q →
                    cyclicRegularOuterKernel B D p q →
                      canonicalTransportedRefinement
                        (G := G) (Ω := Ω) B B0 Q0 ∧
                        let Q := transportedPartition
                          (G := G) (Ω := Ω) B B0 Q0
                        ∃ r : ℕ, (r = p ∨ r = q) ∧
                          cellSize Q r ∧
                            uniqueCharacteristicSubgroup C r ∧
                              uniqueCharacteristicSubgroup D r ∧
                                ∃ KC KD : Subgroup G,
                                  characteristicSubgroupWithin C KC r ∧
                                    characteristicSubgroupWithin D KD r ∧
                                      Q = orbitPartition KC ∧
                                        Q = orbitPartition KD

/-- The kernel of the action on a partition consists of elements fixing every
cell setwise. -/
def blockActionKernel {G Ω : Type*} [Group G] [MulAction G Ω]
    (Q : Set (Set Ω)) : Set G :=
  {g | ∀ C ∈ Q, actionImage g C = C}

/-- The block-action kernel is transitive on each cell. -/
def kernelTransitiveOnCells {G Ω : Type*} [Group G] [MulAction G Ω]
    (Q : Set (Set Ω)) : Prop :=
  ∀ C ∈ Q, ∀ x y : Ω, x ∈ C → y ∈ C →
    ∃ g : G, g ∈ blockActionKernel (G := G) (Ω := Ω) Q ∧ g • x = y

/-- A normal block system is the orbit partition of a normal subgroup. -/
def normalBlockSystem {G Ω : Type*} [Group G] [MulAction G Ω]
    (Q : Set (Set Ω)) : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ Q = orbitPartition N

/-- Claim 41179: transitivity of the kernel fixing every `Q`-cell gives a
normal block system. -/
def claim41179_kernelTransitivityNormality : Prop :=
  ∀ (G Ω : Type*) [Group G] [MulAction G Ω]
    (Q : Set (Set Ω)),
    partitionOf Q →
      invariantPartition (G := G) (Ω := Ω) Q →
        kernelTransitiveOnCells (G := G) (Ω := Ω) Q →
          normalBlockSystem (G := G) (Ω := Ω) Q

/-- Claim 41180: in every finite transitive outer-block action of the stated
kind, each nontrivial local block system canonically globalizes to the normal
common characteristic-prime orbit refinement. -/
def claim41180_allPrimesGlobalization : Prop :=
  ∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p ≠ q →
    ∀ (G Ω : Type*) [Group G] [Fintype Ω] [MulAction G Ω]
      (B : Set (Set Ω)) (C D : Subgroup G),
      transitiveAction (G := G) (Ω := Ω) →
        outerPartition (G := G) (Ω := Ω) B →
          outerBlocksHaveSize B (p * q) →
            cyclicRegularOuterKernel B C p q →
              cyclicRegularOuterKernel B D p q →
                ∀ B0 : Set Ω, B0 ∈ B →
                  ∀ Q0 : Set (Set Ω),
                    localBlockSystem (G := G) (Ω := Ω) B0 Q0 →
                      nontrivialLocalPartition B0 Q0 →
                        canonicalTransportedRefinement
                          (G := G) (Ω := Ω) B B0 Q0 ∧
                          let Q := transportedPartition
                            (G := G) (Ω := Ω) B B0 Q0
                          ∃ r : ℕ, (r = p ∨ r = q) ∧
                            cellSize Q r ∧
                              normalBlockSystem
                                (G := G) (Ω := Ω) Q ∧
                                uniqueCharacteristicSubgroup C r ∧
                                  uniqueCharacteristicSubgroup D r ∧
                                    ∃ KC KD : Subgroup G,
                                      characteristicSubgroupWithin C KC r ∧
                                        characteristicSubgroupWithin D KD r ∧
                                          Q = orbitPartition KC ∧
                                            Q = orbitPartition KD

end
end MathlibPlus.Open.ResearchFormalization.R1346
