import Mathlib

namespace MathlibPlus.GraphTheory

/-- Claim 26148 with both graph-theoretic phrases expanded.  A five-vertex
induced subgraph contains a cycle exactly when its induced graph is not
acyclic; the induced-forest bound quantifies over all finite vertex sets. -/
theorem cyclicFive_iff_inducedForestNumberLeFour_claim26148 {V : Type*}
    (G : SimpleGraph V) :
    (∀ s : Finset V, s.card = 5 →
      ¬ (G.induce (s : Set V)).IsAcyclic) ↔
    (∀ s : Finset V, (G.induce (s : Set V)).IsAcyclic → s.card ≤ 4) := by
  constructor
  · intro h s hs
    by_contra hnot
    have h5 : 5 ≤ s.card := by omega
    obtain ⟨t, hts, htcard⟩ := s.exists_subset_card_eq h5
    have hts' : (t : Set V) ⊆ (s : Set V) := by
      intro x hx
      exact hts hx
    have htacyc : (G.induce (t : Set V)).IsAcyclic := by
      exact hs.comap (G.induceHomOfLE hts').toHom
        (G.induceHomOfLE hts').injective
    exact h t htcard htacyc
  · intro h s hs5 hacyc
    have hle := h s hacyc
    omega

end MathlibPlus.GraphTheory
