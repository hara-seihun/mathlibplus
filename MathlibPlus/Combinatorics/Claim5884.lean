import Mathlib

namespace MathlibPlus.Combinatorics.Claim5884

/-- The source range `2 ≤ r ≤ n - 2` for an ordered root. -/
def admissibleRootParameters (n r : ℕ) : Prop := 2 ≤ r ∧ r ≤ n - 2

/-- The exact root neighborhood of an outside vertex, as a subset of `Fin r`. -/
noncomputable def rootNeighborhood {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n) (v : Fin n) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun i => G.Adj (ρ i) v)

/-- The number `x_S(ρ)` of outside vertices with exact root neighborhood `S`. -/
noncomputable def exactRootNeighborhoodCount {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n) (S : Finset (Fin r)) : ℕ :=
  (Finset.univ.filter (fun v =>
    v ∉ Set.range ρ ∧ rootNeighborhood G ρ v = S)).card

theorem mem_rootNeighborhood {n r : ℕ}
    (G : SimpleGraph (Fin n)) (ρ : Fin r ↪ Fin n) (v : Fin n) (i : Fin r) :
    i ∈ rootNeighborhood G ρ v ↔ G.Adj (ρ i) v := by
  classical
  simp [rootNeighborhood]

end MathlibPlus.Combinatorics.Claim5884
