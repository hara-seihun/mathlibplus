import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Tactic.FinCases

namespace MathlibPlus.Combinatorics.Claim12644

/-- The four explicit local witnesses from the deleted-card `P₄` example preserve
adjacency on the vertices remaining after the indicated deletion. -/
theorem localOddWitness_deleted_card_automorphism :
    let P : SimpleGraph (Fin 4) := SimpleGraph.pathGraph 4
    let w : Fin 4 → Equiv.Perm (Fin 4) := fun i =>
      if i = 0 then Equiv.swap 1 3
      else if i = 1 then Equiv.swap 2 3
      else if i = 2 then Equiv.swap 0 1
      else Equiv.swap 0 2
    ∀ i : Fin 4,
      ∃ f : {x : Fin 4 // x ≠ i} → {x : Fin 4 // x ≠ i},
        Function.Bijective f ∧
        (∀ u, (f u).val = w i u.val) ∧
        (∀ u v, (P.induce {x : Fin 4 | x ≠ i}).Adj (f u) (f v) ↔
          (P.induce {x : Fin 4 | x ≠ i}).Adj u v) := by
  dsimp
  intro i
  fin_cases i
  · let f : {x : Fin 4 // x ≠ 0} → {x : Fin 4 // x ≠ 0} := fun u =>
      ⟨(Equiv.swap 1 3) u.val, by
        fin_cases u <;> simp [Equiv.swap_apply_def]
      ⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · native_decide
    · intro u
      rfl
    · intro u v
      fin_cases u <;> fin_cases v <;>
        simp [f, SimpleGraph.induce, SimpleGraph.pathGraph_adj,
          Equiv.swap_apply_def]
  · let f : {x : Fin 4 // x ≠ 1} → {x : Fin 4 // x ≠ 1} := fun u =>
      ⟨(Equiv.swap 2 3) u.val, by
        fin_cases u <;> simp [Equiv.swap_apply_def]
      ⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · native_decide
    · intro u
      rfl
    · intro u v
      fin_cases u <;> fin_cases v <;>
        simp [f, SimpleGraph.induce, SimpleGraph.pathGraph_adj,
          Equiv.swap_apply_def]
  · let f : {x : Fin 4 // x ≠ 2} → {x : Fin 4 // x ≠ 2} := fun u =>
      ⟨(Equiv.swap 0 1) u.val, by
        fin_cases u <;> simp [Equiv.swap_apply_def]
      ⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · native_decide
    · intro u
      rfl
    · intro u v
      fin_cases u <;> fin_cases v <;>
        simp [f, SimpleGraph.induce, SimpleGraph.pathGraph_adj,
          Equiv.swap_apply_def]
  · let f : {x : Fin 4 // x ≠ 3} → {x : Fin 4 // x ≠ 3} := fun u =>
      ⟨(Equiv.swap 0 2) u.val, by
        fin_cases u <;> simp [Equiv.swap_apply_def]
      ⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · native_decide
    · intro u
      rfl
    · intro u v
      fin_cases u <;> fin_cases v <;>
        simp [f, SimpleGraph.induce, SimpleGraph.pathGraph_adj,
          Equiv.swap_apply_def]

end MathlibPlus.Combinatorics.Claim12644
