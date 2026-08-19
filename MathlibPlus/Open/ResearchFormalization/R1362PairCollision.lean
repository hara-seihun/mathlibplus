import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1362PairCollision

noncomputable section

/-- Claim 31010: after the exact nonlinear base permutation normalization on
`F₃²`, an active unordered pair has output `ρ⁻¹(ρ(u)+ρ(v))`; a four-point
support therefore has at most six distinct pair outputs. -/
def normalizedPairCollisionOutput_claim31010 : Prop :=
  let B := Fin 2 → ZMod 3
  ∀ (ρ : Equiv.Perm B) (S : Finset B),
    S.card = 4 →
      Set.ncard {m : B |
        ∃ u v : B, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧
          m = ρ.symm (ρ u + ρ v)} ≤ 6

/-- Claim 31018: the exact ordered four-tuples of displacement subgroups of
`C₃²` split into the stated full-span, line-contained, and pairwise-generation
census classes. -/
def fullJointSpanProfileCensus_claim31018 : Prop :=
  let B := Fin 2 → ZMod 3
  let Profiles := Fin 4 → AddSubgroup B
  let fullJoint := fun W : Profiles =>
    AddSubgroup.closure (⋃ i : Fin 4, (W i : Set B)) = ⊤
  let pairwise := fun W : Profiles =>
    ∀ i j : Fin 4, i ≠ j →
      AddSubgroup.closure ((W i : Set B) ∪ (W j : Set B)) = ⊤
  let lineContained := fun W : Profiles =>
    ∃ L : AddSubgroup B,
      Nat.card L = 3 ∧ ∀ i : Fin 4, W i ≤ L
  Fintype.card Profiles = 1296 ∧
    Nat.card {W : Profiles // fullJoint W} = 1235 ∧
    Nat.card {W : Profiles // ¬ fullJoint W} = 61 ∧
    Nat.card {L : AddSubgroup B // Nat.card L = 3} = 4 ∧
    (∀ W : Profiles,
      ¬ fullJoint W ↔
        ((∀ i : Fin 4, W i = ⊥) ∨ lineContained W)) ∧
    Nat.card {W : Profiles // fullJoint W ∧ pairwise W} = 213 ∧
    Nat.card {W : Profiles // fullJoint W ∧ ¬ pairwise W} =
      1235 - 213 ∧
    Nat.card {W : Profiles // fullJoint W ∧ ¬ pairwise W} = 1022

end

end MathlibPlus.Open.ResearchFormalization.R1362PairCollision
