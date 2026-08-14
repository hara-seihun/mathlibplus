import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Adjacency in the path `0-1-2-3`. -/
def pathFourAdjacent (i j : Fin 4) : Prop :=
  i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- An automorphism of the card obtained by deleting `i` from `P₄`. -/
def pathFourDeletedAutomorphism (i : Fin 4) (σ : Equiv.Perm (Fin 4)) : Prop :=
  σ i = i ∧
    ∀ x y : Fin 4,
      x ≠ i → y ≠ i →
        (pathFourAdjacent x y ↔ pathFourAdjacent (σ x) (σ y))

/-- Claim 12642. -/
def oddCosetP4LocalWitnesses : Prop :=
  pathFourDeletedAutomorphism 0 (Equiv.swap (1 : Fin 4) (3 : Fin 4)) ∧
    pathFourDeletedAutomorphism 1 (Equiv.swap (2 : Fin 4) (3 : Fin 4)) ∧
    pathFourDeletedAutomorphism 2 (Equiv.swap (0 : Fin 4) (1 : Fin 4)) ∧
    pathFourDeletedAutomorphism 3 (Equiv.swap (0 : Fin 4) (2 : Fin 4))

/-- Claim 12643. -/
def everyP4LocalWitnessIsOddAndFixesDeletion : Prop :=
  (Equiv.Perm.sign (Equiv.swap (1 : Fin 4) (3 : Fin 4)) = (-1 : ℤˣ) ∧
      (Equiv.swap (1 : Fin 4) (3 : Fin 4)) 0 = 0) ∧
    (Equiv.Perm.sign (Equiv.swap (2 : Fin 4) (3 : Fin 4)) = (-1 : ℤˣ) ∧
      (Equiv.swap (2 : Fin 4) (3 : Fin 4)) 1 = 1) ∧
    (Equiv.Perm.sign (Equiv.swap (0 : Fin 4) (1 : Fin 4)) = (-1 : ℤˣ) ∧
      (Equiv.swap (0 : Fin 4) (1 : Fin 4)) 2 = 2) ∧
    (Equiv.Perm.sign (Equiv.swap (0 : Fin 4) (2 : Fin 4)) = (-1 : ℤˣ) ∧
      (Equiv.swap (0 : Fin 4) (2 : Fin 4)) 3 = 3)

/-- Claim 12646. -/
def oddCosetContainsNoGlobalP4Automorphism : Prop :=
  ¬ ∃ σ : Equiv.Perm (Fin 4),
      Equiv.Perm.sign σ = (-1 : ℤˣ) ∧
        ∀ i j : Fin 4,
          pathFourAdjacent i j ↔ pathFourAdjacent (σ i) (σ j)

end MathlibPlus.Open.ResearchFormalization
