import Mathlib.Combinatorics.SimpleGraph.Basic

namespace MathlibPlus.GraphTheory.Claim9136

/-- Complement invariance of `(5,5)`-goodness from claim 9136.  A graph is
represented as good when it has neither a five-vertex clique nor a five-vertex
independent set; the two conditions are written directly to keep the claim's
meaning explicit without adding a new graph predicate. -/
theorem complementGood55_claim9136 {V : Type*} (G : SimpleGraph V) :
    let good : SimpleGraph V → Prop := fun H =>
      (¬ ∃ s : Finset V, s.card = 5 ∧
          ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → H.Adj u v) ∧
      (¬ ∃ s : Finset V, s.card = 5 ∧
          ∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬ H.Adj u v)
    good G ↔ good Gᶜ := by
  dsimp
  have hcl (s : Finset V) :
      (∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → Gᶜ.Adj u v) ↔
        (∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬ G.Adj u v) := by
    constructor
    · intro h u v hu hv huv
      exact (G.compl_adj u v).mp (h hu hv huv) |>.2
    · intro h u v hu hv huv
      exact (G.compl_adj u v).mpr ⟨huv, h hu hv huv⟩
  have hind (s : Finset V) :
      (∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → ¬ Gᶜ.Adj u v) ↔
        (∀ ⦃u v : V⦄, u ∈ s → v ∈ s → u ≠ v → G.Adj u v) := by
    constructor
    · intro h u v hu hv huv
      by_contra hG
      exact h hu hv huv ((G.compl_adj u v).mpr ⟨huv, hG⟩)
    · intro h u v hu hv huv hcomp
      exact (G.compl_adj u v).mp hcomp |>.2 (h hu hv huv)
  constructor
  · rintro ⟨hNoClique, hNoIndependent⟩
    constructor
    · intro hClique
      rcases hClique with ⟨s, hs, hrel⟩
      exact hNoIndependent ⟨s, hs, (hcl s).mp hrel⟩
    · intro hIndependent
      rcases hIndependent with ⟨s, hs, hrel⟩
      exact hNoClique ⟨s, hs, (hind s).mp hrel⟩
  · rintro ⟨hNoClique, hNoIndependent⟩
    constructor
    · intro hClique
      rcases hClique with ⟨s, hs, hrel⟩
      exact hNoIndependent ⟨s, hs, (hind s).mpr hrel⟩
    · intro hIndependent
      rcases hIndependent with ⟨s, hs, hrel⟩
      exact hNoClique ⟨s, hs, (hcl s).mpr hrel⟩

end MathlibPlus.GraphTheory.Claim9136
