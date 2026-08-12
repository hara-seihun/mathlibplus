import Mathlib

namespace MathlibPlus.GraphTheory.Claim44016

open SimpleGraph

/-- A vertex is missed by a graph when it has no incident edge. -/
def missesVertex {V : Type*} (G : SimpleGraph V) (v : V) : Prop :=
  ∀ w, ¬G.Adj v w

theorem union_misses_join_of_distinct_missed_vertices
    {V : Type*} (G₁ G₂ : SimpleGraph V) (u v : V) (huv : u ≠ v)
    (h₁ : missesVertex G₁ u) (h₂ : missesVertex G₂ v) :
    ¬(G₁ ⊔ G₂).Adj u v := by
  intro h
  rw [sup_adj] at h
  rcases h with h | h
  · exact h₁ v h
  · exact h₂ u (by simpa [adj_comm] using h)

theorem completeGraph_not_covered_by_two_missed_parts
    {V : Type*} [Finite V] (u v : V) (huv : u ≠ v)
    (G₁ G₂ : SimpleGraph V) (h₁ : missesVertex G₁ u)
    (h₂ : missesVertex G₂ v) :
    ¬((⊤ : SimpleGraph V) ≤ G₁ ⊔ G₂) := by
  intro hcover
  have hedge : (⊤ : SimpleGraph V).Adj u v := by simp [huv]
  have : (G₁ ⊔ G₂).Adj u v := hcover hedge
  exact union_misses_join_of_distinct_missed_vertices G₁ G₂ u v huv h₁ h₂ this

end MathlibPlus.GraphTheory.Claim44016
