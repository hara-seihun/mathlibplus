import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Formalization of admitted claim 42302.  A core family is a set of sets;
`D` and `K` retain the displayed subset conditions, while `E` and `Q` retain
respectively the union and set-difference definitions.  The normalized-slice
hypothesis is represented by `R ∉ G`. -/
def comparableAndIncomparableRegions_claim42302 : Prop :=
  ∀ (α : Type*) (G : Set (Set α)) (R : Set α),
    R ∉ G →
      let D : Set (Set α) := {A | A ∈ G ∧ A ⊆ R}
      let K : Set (Set α) := {A | A ∈ G ∧ R ⊆ A}
      let E : Set (Set α) := D ∪ K
      let Q : Set (Set α) := G \ E
      D ∩ K = ∅ ∧ E = D ∪ K ∧ Q = G \ E

end MathlibPlus.Open.Combinatorics

namespace MathlibPlus.Combinatorics

theorem comparableAndIncomparableRegions_claim42302_proved :
    MathlibPlus.Open.Combinatorics.comparableAndIncomparableRegions_claim42302 := by
  intro α G R hR
  let D : Set (Set α) := {A | A ∈ G ∧ A ⊆ R}
  let K : Set (Set α) := {A | A ∈ G ∧ R ⊆ A}
  let E : Set (Set α) := D ∪ K
  let Q : Set (Set α) := G \ E
  have hDK : D ∩ K = ∅ := by
    ext A
    constructor
    · intro h
      rcases h with ⟨hD, hK⟩
      have hAR : A ⊆ R := hD.2
      have hRA : R ⊆ A := hK.2
      have hEq : A = R := Set.Subset.antisymm hAR hRA
      exact (hR (hEq ▸ hD.1)).elim
    · intro h
      exact h.elim
  exact ⟨hDK, rfl, rfl⟩

end MathlibPlus.Combinatorics
