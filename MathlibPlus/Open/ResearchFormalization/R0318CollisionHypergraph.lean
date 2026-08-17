import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0318CollisionHypergraph

noncomputable section

open scoped BigOperators

/-- Two factor vertices are incident to a common collision hyperedge. -/
def collisionIncident
    {k m : ℕ} (S : Fin m → Finset (Fin k)) (u v : Fin k) : Prop :=
  ∃ e : Fin m, u ∈ S e ∧ v ∈ S e

/-- Connectedness of a finite collision hypergraph, with every collision
hyperedge carrying at least two factor vertices. -/
def connectedCollisionHypergraph
    {k m : ℕ} (S : Fin m → Finset (Fin k)) : Prop :=
  (∀ e : Fin m, 2 ≤ (S e).card) ∧
    ∀ u v : Fin k, Relation.ReflTransGen (collisionIncident S) u v

/-- The collision-hypergraph weighted size, i.e. edge redundancy. -/
def collisionWeightedSize
    {k m : ℕ} (S : Fin m → Finset (Fin k)) : ℕ :=
  ∑ e : Fin m, (S e).card - 1

/-- Claim 19776: a connected collision hypergraph on `k` factor vertices has
weighted size at least `k-1`, the exact edge-redundancy bound for a connected
cover. -/
def connectedHypergraphRedundancy_claim19776 : Prop :=
  ∀ (k m : ℕ) (S : Fin m → Finset (Fin k)),
    connectedCollisionHypergraph S →
      collisionWeightedSize S ≥ k - 1

end

end MathlibPlus.Open.ResearchFormalization.R0318CollisionHypergraph
