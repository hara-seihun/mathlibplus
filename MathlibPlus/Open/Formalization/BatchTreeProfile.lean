import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

private def edgeAdj (E : Finset (Fin 12 × Fin 12))
    (x y : Fin 12) : Prop :=
  x ≠ y ∧ ((x, y) ∈ E ∨ (y, x) ∈ E)

private def edgeGraph (E : Finset (Fin 12 × Fin 12)) : SimpleGraph (Fin 12) :=
  { Adj := edgeAdj E
    symm := ⟨by
      intro x y h
      rcases h with ⟨hxy, hE | hE⟩
      · exact ⟨hxy.symm, Or.inr hE⟩
      · exact ⟨hxy.symm, Or.inl hE⟩⟩
    loopless := ⟨by
      intro x h
      exact h.1 rfl⟩ }

private def explicitDegree (E : Finset (Fin 12 × Fin 12)) (x : Fin 12) : Nat := by
  classical
  exact (Finset.univ.filter (edgeAdj E x)).card

private def neighborDegreeCount (E : Finset (Fin 12 × Fin 12))
    (x : Fin 12) (n : Nat) : Nat := by
  classical
  exact (Finset.univ.filter (fun y => edgeAdj E x y ∧ explicitDegree E y = n)).card

private def degreeProfile (E : Finset (Fin 12 × Fin 12)) : Prop := by
  classical
  exact
    (∀ x : Fin 12, explicitDegree E x ≤ 4) ∧
    (Finset.univ.filter (fun x => explicitDegree E x = 4)).card = 1 ∧
    (Finset.univ.filter (fun x => explicitDegree E x = 3)).card = 2 ∧
    (Finset.univ.filter (fun x => explicitDegree E x = 2)).card = 3 ∧
    (Finset.univ.filter (fun x => explicitDegree E x = 1)).card = 6

/-- Claim 54622: the explicit order-12 profile twin. -/
def claim_54622 : Prop := by
  classical
  let E_A : Finset (Fin 12 × Fin 12) :=
    {((0 : Fin 12), 7), (0, 10), (0, 11), (0, 1), (1, 2), (1, 5),
      (2, 3), (2, 4), (5, 6), (7, 8), (8, 9)}
  let E_B : Finset (Fin 12 × Fin 12) :=
    {((0 : Fin 12), 7), (0, 10), (0, 1), (1, 2), (1, 5), (1, 6),
      (2, 3), (2, 4), (7, 8), (8, 9), (10, 11)}
  let a₄ : Fin 12 := 0
  let b₄ : Fin 12 := 1
  exact
    SimpleGraph.IsTree (edgeGraph E_A) ∧
    SimpleGraph.IsTree (edgeGraph E_B) ∧
    degreeProfile E_A ∧ degreeProfile E_B ∧
    explicitDegree E_A a₄ = 4 ∧ explicitDegree E_B b₄ = 4 ∧
    (neighborDegreeCount E_A a₄ 1 = 2 ∧
      neighborDegreeCount E_A a₄ 2 = 1 ∧ neighborDegreeCount E_A a₄ 3 = 1) ∧
    (neighborDegreeCount E_B b₄ 1 = 2 ∧
      neighborDegreeCount E_B b₄ 3 = 2) ∧
    (¬ ∃ e : Equiv.Perm (Fin 12),
      ∀ x y, edgeAdj E_A x y ↔ edgeAdj E_B (e x) (e y))

end
end MathlibPlus.Open.FormalizationBatch
