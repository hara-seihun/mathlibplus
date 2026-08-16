import Mathlib

namespace MathlibPlus.Open.Graph

def no_large_prime_automorphism_on_43_vertices : Prop :=
  ∀ (V : Type*) [Fintype V],
    Fintype.card V = 43 →
      ∀ G : SimpleGraph V,
        (¬ ∃ s : Set V, s.Finite ∧ s.ncard = 5 ∧ G.IsClique s) →
          (¬ ∃ s : Set V,
            s.Finite ∧ s.ncard = 5 ∧ s.Pairwise (fun v w => ¬ G.Adj v w)) →
            ∀ (p : ℕ), p.Prime → 11 ≤ p →
              ∀ e : G ≃g G, orderOf e.toEquiv ≠ p

end MathlibPlus.Open.Graph
