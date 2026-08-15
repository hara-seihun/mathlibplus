import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Separation does not identify a union-closed family with its join-irreducible core. -/
def claim3366 : Prop :=
  let U : Finset (Fin 4) := {1, 2, 3}
  let F : Finset (Finset (Fin 4)) := {∅, {1, 2}, {1, 3}, {1, 2, 3}}
  let L : Finset (Finset (Fin 4)) :=
    F.image (fun A => U \ A)
  let incidence : Fin 4 → Set (Finset (Fin 4)) :=
    fun i => {A | A ∈ F ∧ i ∈ A}
  let closure : Finset (Fin 4) → Finset (Fin 4) :=
    fun S => U ∩ (L.filter (fun A => S ⊆ A)).inf id
  let joinIrreducible : Finset (Fin 4) → Prop :=
    fun x =>
      x ∈ L ∧ x ≠ ∅ ∧
        ∀ y z : Finset (Fin 4),
          y ∈ L → z ∈ L → closure (y ∪ z) = x → y = x ∨ z = x
  let coordinateCore : Finset (Fin 4) :=
    U.filter (fun i => joinIrreducible (closure {i}))
  let coreLattice : Finset (Finset (Fin 4)) :=
    coordinateCore.powerset.image closure
  (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) ∧
    (∀ i j : Fin 4,
      i ∈ U → j ∈ U → i ≠ j →
        ∃ A, A ∈ F ∧
          ((i ∈ A ∧ j ∉ A) ∨ (j ∈ A ∧ i ∉ A))) ∧
    (∀ i j : Fin 4,
      i ∈ U → j ∈ U → i ≠ j → incidence i ≠ incidence j) ∧
    closure {1} = U ∧
    (∃ x y : Finset (Fin 4),
      x ∈ L ∧ y ∈ L ∧
        x ≠ closure {1} ∧ y ≠ closure {1} ∧
        closure (x ∪ y) = closure {1}) ∧
    (∀ x y : Finset (Fin 4),
      x ∈ L → y ∈ L → closure (x ∪ y) ∈ L) ∧
    coordinateCore = {2, 3} ∧
    coordinateCore.card = 2 ∧
    coordinateCore.powerset.card = 4 ∧
    coreLattice = L

end MathlibPlus.Open.ResearchFormalization
