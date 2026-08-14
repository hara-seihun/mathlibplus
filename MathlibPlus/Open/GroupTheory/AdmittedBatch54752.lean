import Mathlib

namespace MathlibPlus.Open.GroupTheory.AdmittedBatch54752

noncomputable section

abbrev V5 := ZMod 5 × ZMod 5 × ZMod 5

private def q1 : V5 → V5 := fun p =>
  (p.1 + p.2.1 ^ 3, p.2.1 + p.2.2 ^ 3, p.2.2)

private def q1Inv : V5 → V5 := fun p =>
  (p.1 - (p.2.1 - p.2.2 ^ 3) ^ 3, p.2.1 - p.2.2 ^ 3, p.2.2)

private def q2 : V5 → V5 := fun p =>
  (p.1 + p.2.1 ^ 3, p.2.1 + (p.1 + p.2.1 ^ 3) ^ 3, p.2.2)

private def q2Inv : V5 → V5 := fun p =>
  (p.1 - (p.2.1 - p.1 ^ 3) ^ 3, p.2.1 - p.1 ^ 3, p.2.2)

/-- The signed difference transport used to generate the partition. -/
private def transportRelation (q qi : V5 → V5) (s t : V5) : Prop :=
  ∃ v : V5,
    t = qi (q (v + s) - q v) ∨
      t = -qi (q (v + s) - q v)

private def transportPartition (q qi : V5 → V5) (s t : V5) : Prop :=
  Relation.EqvGen (transportRelation q qi) s t

/-- A list is the exact list of blocks when its elements are the equivalence
classes of the signed transport relation, including connectivity inside each
listed block and the listed cardinalities. -/
private def exactTransportBlocks (q qi : V5 → V5)
    (blocks : List (Set V5)) (sizes : List ℕ) : Prop :=
  List.map (fun B : Set V5 => B.ncard) blocks = sizes ∧
    (∀ s t : V5,
      transportPartition q qi s t ↔
        ∃ B ∈ blocks, s ∈ B ∧ t ∈ B) ∧
    (∀ B : Set V5, B ∈ blocks →
      ∀ s ∈ B, ∀ t ∈ B, transportPartition q qi s t)

private def q1Blocks : List (Set V5) :=
  [
    {0},
    {p | p.2.1 = 0 ∧ p.2.2 = 0 ∧ (p.1 = 1 ∨ p.1 = -1)},
    {p | p.2.1 = 0 ∧ p.2.2 = 0 ∧ (p.1 = 2 ∨ p.1 = -2)},
    {p | p.2.2 = 0 ∧ (p.2.1 = 1 ∨ p.2.1 = -1)},
    {p | p.2.2 = 0 ∧ (p.2.1 = 2 ∨ p.2.1 = -2)},
    {p | p.2.2 = 1 ∨ p.2.2 = -1},
    {p | p.2.2 = 2 ∨ p.2.2 = -2}
  ]

private def q2Blocks : List (Set V5) :=
  [
    {0},
    {p | p.1 = 0 ∧ p.2.1 = 0 ∧ (p.2.2 = 1 ∨ p.2.2 = -1)},
    {p | p.1 = 0 ∧ p.2.1 = 0 ∧ (p.2.2 = 2 ∨ p.2.2 = -2)},
    {p | (p.1, p.2.1) ≠ (0, 0) ∧ p.2.2 = 0},
    {p | (p.1, p.2.1) ≠ (0, 0) ∧ (p.2.2 = 1 ∨ p.2.2 = -1)},
    {p | (p.1, p.2.1) ≠ (0, 0) ∧ (p.2.2 = 2 ∨ p.2.2 = -2)}
  ]

/-- Claim 54752: the two displayed odd cubic shears are permutations fixing
zero, with inverses obtained by reversing the shears. -/
def twoOddCubicPermutations_claim54752 : Prop :=
  Function.Bijective q1 ∧
    Function.Bijective q2 ∧
    q1 0 = 0 ∧ q2 0 = 0 ∧
    (∀ p : V5, q1Inv (q1 p) = p ∧ q1 (q1Inv p) = p) ∧
    (∀ p : V5, q2Inv (q2 p) = p ∧ q2 (q2Inv p) = p)

/-- Claim 54755: the seven listed blocks are exactly the signed difference
transport classes of the first cubic shear, in the stated order and sizes. -/
def q1SignedDifferenceBlocks_claim54755 : Prop :=
  exactTransportBlocks q1 q1Inv q1Blocks [1, 2, 2, 10, 10, 50, 50]

/-- Claim 54757: the six listed blocks are exactly the signed difference
transport classes of the second cubic shear, in the stated order and sizes. -/
def q2SignedDifferenceBlocks_claim54757 : Prop :=
  exactTransportBlocks q2 q2Inv q2Blocks [1, 2, 2, 24, 48, 48]

end
end MathlibPlus.Open.GroupTheory.AdmittedBatch54752
