import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- A Boolean adjacency relation satisfying symmetry and irreflexivity is
interpreted as the adjacency relation of a Mathlib simple graph. -/
def claim44505 : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
    (∀ i j, adj i j = true → adj j i = true) →
    (∀ i, adj i i = false) →
    ∃ G : SimpleGraph (Fin n),
      ∀ i j, G.Adj i j ↔ adj i j = true

end MathlibPlus.Open.ResearchFormalizationBatch
