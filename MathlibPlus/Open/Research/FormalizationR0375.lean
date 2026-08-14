import Mathlib

namespace MathlibPlus.Open.Research.R0375

noncomputable section
open scoped BigOperators

/-- The number of distinct relabelings of `G` that contain a fixed spanning `F`. -/
def hostOrbitIncidence (n : ℕ) (G F : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard
    ((Set.range (fun σ : Equiv.Perm (Fin n) => G.map σ)) ∩
      {G' : SimpleGraph (Fin n) | F ≤ G'})

/-- The order of the labeled automorphism group of a finite graph. -/
def automorphismCard (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard {σ : Equiv.Perm (Fin n) | G.map σ = G}

/-- The number of spanning subgraphs of `G` isomorphic to `F`. -/
def spanningSubgraphCount (n : ℕ) (F G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard {K : SimpleGraph (Fin n) | K ≤ G ∧ Nonempty (K ≃g F)}

/-- Exact orbit--stabilizer incidence formula. -/
def exactOrbitStabilizerSubgraphCount : Prop :=
  ∀ (n : ℕ) (F G : SimpleGraph (Fin n)), F ≤ G →
    (hostOrbitIncidence n G F : ℚ) =
      (spanningSubgraphCount n F G : ℚ) * automorphismCard n F /
        automorphismCard n G

/-- The number of edges of a finite labeled graph. -/
def edgeCount {n : ℕ} (F : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard F.edgeSet

/-- The host statistic obtained by minimizing the incidence bound over spanning subgraphs. -/
def hostStatistic (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {q : ℕ | ∃ F : SimpleGraph (Fin n), F ≤ G ∧
    q = edgeCount F + 1 + Nat.log 2 (hostOrbitIncidence n G F)}

end
end MathlibPlus.Open.Research.R0375
