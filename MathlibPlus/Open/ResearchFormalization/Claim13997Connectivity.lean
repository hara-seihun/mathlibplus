import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim13997

/-- The `m = 2` orbit has at least three points on each side, and the
balanced bipartite minimum-degree condition forces one connected component. -/
def connectivity_m2_claim13997 : Prop :=
  ∀ (n m : ℕ),
    m = 2 →
    n = 2 * (n / 2) →
    3 ≤ n / 2 →
    ∀ (G : SimpleGraph (Sum (Fin (n / 2)) (Fin (n / 2)))),
      (∀ u v : Fin (n / 2),
        ¬ G.Adj (Sum.inl u) (Sum.inl v)) →
      (∀ u v : Fin (n / 2),
        ¬ G.Adj (Sum.inr u) (Sum.inr v)) →
      (∀ u : Fin (n / 2),
        Set.ncard {v : Fin (n / 2) |
          G.Adj (Sum.inl u) (Sum.inr v)} ≥ n / 2 - 1) →
      (∀ v : Fin (n / 2),
        Set.ncard {u : Fin (n / 2) |
          G.Adj (Sum.inl u) (Sum.inr v)} ≥ n / 2 - 1) →
      G.Connected

end MathlibPlus.Open.ResearchFormalization.Claim13997
