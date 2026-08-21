-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/-- Claim 35803, with the twelve cube edges indexed by `Fin 12`.  The six
coordinate squares are the six displayed four-edge subsets. -/
theorem cubeQ3_edge_census :
    let E : Finset (Fin 12) := Finset.univ
    let squares : Finset (Finset (Fin 12)) :=
      {({0, 2, 4, 6} : Finset (Fin 12)),
       {1, 3, 5, 7},
       {0, 1, 8, 10},
       {2, 3, 9, 11},
       {4, 5, 8, 9},
       {6, 7, 10, 11}}
    let squareFree : Finset (Fin 12) → Prop :=
      fun S => ∀ Q ∈ squares, ¬ Q ⊆ S
    let free : Finset (Finset (Fin 12)) := E.powerset.filter squareFree
    E.powerset.card = 4096 ∧
      free.card = 2902 ∧
      (∀ S ∈ free, S.card ≤ 9) ∧
      (∃ S ∈ free, S.card = 9) := by
  native_decide

end MathlibPlus.Combinatorics
