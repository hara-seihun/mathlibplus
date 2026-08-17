import MathlibPlus.Combinatorics.Claim22656

namespace MathlibPlus.Open.ResearchFormalization.R0557Claim22646

open MathlibPlus.Combinatorics.Claim22656

noncomputable section

/-- The exact guarded punctured cube: all nonempty subsets of `P`, together
    with the one guarded member containing `P`, `z`, and `c`. -/
def guardedPuncturedCubeFamily {α : Type*} [DecidableEq α]
    (P : Finset α) (z c : α) : Finset (Finset α) :=
  P.powerset.erase ∅ ∪ {P ∪ {z, c}}

/-- Two family members form a toggle pair at `x` when they differ only in `x`.
    The orientation records one member containing `x` and the other omitting it. -/
def hasTogglePair {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : Prop :=
  ∃ A B : Finset α,
    A ∈ F ∧ B ∈ F ∧ A.erase x = B.erase x ∧ x ∈ A ∧ x ∉ B

/-- Omission count minus containment count for a coordinate. -/
def coordinateDeficit {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : ℤ :=
  ((F.filter (fun A => x ∉ A)).card : ℤ) -
    ((F.filter (fun A => x ∈ A)).card : ℤ)

/-- Claim 22646: the exact guarded punctured-cube family is union-closed,
    has the stated size and coordinate support properties, has no toggle at
    `z`, and has the displayed deficits. -/
def guardedPuncturedCube_claim22646 : Prop :=
  ∀ {α : Type*} [DecidableEq α]
    (r : ℕ) (P : Finset α) (z c : α),
    2 ≤ r → P.card = r → z ∉ P → c ∉ P → z ≠ c →
      let F := guardedPuncturedCubeFamily P z c
      let support := P ∪ {z, c}
      unionClosed F ∧
        F.card = 2 ^ r ∧
        (∀ x ∈ support, ∃ A ∈ F, x ∉ A) ∧
        (∀ x ∈ support, ∃ A ∈ F, x ∈ A) ∧
        ¬ hasTogglePair F z ∧
        coordinateDeficit F z = (2 : ℤ) ^ r - 2 ∧
        coordinateDeficit F c = (2 : ℤ) ^ r - 2 ∧
        (∀ p ∈ P, coordinateDeficit F p = -2)

end

end MathlibPlus.Open.ResearchFormalization.R0557Claim22646
