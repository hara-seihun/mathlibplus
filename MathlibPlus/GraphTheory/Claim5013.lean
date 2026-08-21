import Mathlib
import MathlibPlus.Basic

namespace MathlibPlus.GraphTheory.Claim5013

/-- A simple graph cannot have exactly one non-isolated vertex. -/
theorem no_unique_nonisolated_claim5013 {V : Type*} (G : SimpleGraph V) :
    ¬ ∃ v, ∀ u, (∃ w, G.Adj u w) ↔ u = v := by
  rintro ⟨v, hv⟩
  have hvv : ∃ w, G.Adj v w := (hv v).mpr rfl
  obtain ⟨w, hvw⟩ := hvv
  by_cases hw : w = v
  · exact G.irrefl (hw ▸ hvw)
  · have hwn : ∃ z, G.Adj w z := ⟨v, G.adj_symm hvw⟩
    exact hw ((hv w).mp hwn)

end MathlibPlus.GraphTheory.Claim5013
