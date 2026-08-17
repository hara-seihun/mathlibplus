import Mathlib

namespace MathlibPlus.Open.Combinatorics.Research1933

noncomputable section
open Classical

/-- The literal incidence support of a ground coordinate in an indexed finite
family of members. -/
def literalSupport {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) (x : α) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => x ∈ F i)

/-- The finite ground set carried by the family. -/
def familyGround {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset α :=
  (Finset.univ : Finset (Fin m)).biUnion F

/-- The nonempty literal incidence supports. -/
def supportPatterns {α : Type*} [Fintype α] [DecidableEq α]
    {m : ℕ} (F : Fin m → Finset α) : Finset (Finset (Fin m)) :=
  (familyGround F).image (literalSupport F)

/-- Laminarity of the literal incidence supports. -/
def laminarSupports {β : Type*} [DecidableEq β]
    (S : Finset (Finset β)) : Prop :=
  ∀ ⦃A B : Finset β⦄, A ∈ S → B ∈ S →
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

/-- Proper inclusion of finite supports. -/
def strictSupportSubset {β : Type*}
    (A B : Finset β) : Prop := A ⊆ B ∧ A ≠ B

/-- The maximal proper support children of a support. -/
noncomputable def maximalProperSupportChildren {β : Type*} [DecidableEq β]
    (S : Finset (Finset β)) (A : Finset β) : Finset (Finset β) :=
  S.filter (fun B =>
    strictSupportSubset B A ∧
      ∀ C : Finset β, C ∈ S → strictSupportSubset B C →
        strictSupportSubset C A → False)

/-- The union of a finite family of support blocks. -/
noncomputable def supportUnion {β : Type*} [DecidableEq β]
    (C : Finset (Finset β)) : Finset β :=
  C.biUnion (fun S => S)

/-- The residual indices of a support after removing its maximal proper
support children. -/
def residualSupport {β : Type*} [DecidableEq β]
    (S : Finset (Finset β)) (A : Finset β) : Finset β :=
  A \ supportUnion (maximalProperSupportChildren S A)

/-- Child blocks and one-member residuals for a distinct uniform family with
laminar literal incidence supports. -/
def claim36325 : Prop :=
  ∀ {α : Type*} [Fintype α] [DecidableEq α]
    (m n : ℕ) (F : Fin m → Finset α),
    Function.Injective F →
    (∀ i : Fin m, (F i).card = n) →
    laminarSupports (supportPatterns F) →
    ∀ S : Finset (Fin m), S ∈ supportPatterns F →
      let C := maximalProperSupportChildren (supportPatterns F) S
      let R := residualSupport (supportPatterns F) S
      (∀ A : Finset (Fin m), A ∈ C → A.Nonempty) ∧
        (∀ A : Finset (Fin m), A ∈ C →
          ∀ B : Finset (Fin m), B ∈ C → A ≠ B → Disjoint A B) ∧
        (S = supportUnion C ∪ R) ∧
        (∀ i : Fin m, i ∈ R →
          ∀ j : Fin m, j ∈ R →
            ∀ U : Finset (Fin m), U ∈ supportPatterns F →
              (i ∈ U ↔ j ∈ U)) ∧
        R.card ≤ 1 ∧
        (∀ i : Fin m, i ∈ S →
          ∃! Q : Finset (Fin m),
            ((Q ∈ C ∧ Q.Nonempty) ∨ (R.Nonempty ∧ Q = R)) ∧
              i ∈ Q)

end
end MathlibPlus.Open.Combinatorics.Research1933
