import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace MathlibPlus.GraphTheory

/-- Claim 44783: the complete and empty simple graphs on two vertices are
nonisomorphic; their edge counts are respectively one and zero. -/
theorem two_vertex_complete_empty_nonisomorphic_claim44783 :
    ¬ Nonempty ((⊤ : SimpleGraph (Fin 2)) ≃g (⊥ : SimpleGraph (Fin 2))) ∧
      (⊤ : SimpleGraph (Fin 2)).edgeFinset.card = 1 ∧
      (⊥ : SimpleGraph (Fin 2)).edgeFinset.card = 0 := by
  classical
  constructor
  · rintro ⟨e⟩
    have h : (⊤ : SimpleGraph (Fin 2)).Adj 0 1 := by simp
    have h' : (⊥ : SimpleGraph (Fin 2)).Adj (e 0) (e 1) :=
      (SimpleGraph.Iso.map_adj_iff e).mpr h
    simpa using h'
  · constructor
    · rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp [Fintype.card_fin]
    · simp only [SimpleGraph.edgeFinset_bot, Finset.card_empty]

end MathlibPlus.GraphTheory
