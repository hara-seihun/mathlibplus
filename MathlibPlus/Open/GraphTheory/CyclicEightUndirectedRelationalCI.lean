import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The cyclic group of order eight has the simultaneous CI property for an
arbitrary family of simple undirected Cayley relations. -/
def cyclicEightUndirectedRelationalCI : Prop :=
  ∀ (ι : Type) (S T : ι → Set (ZMod 8)) (e : ZMod 8 ≃ ZMod 8),
    (∀ i, 0 ∉ S i) →
    (∀ i, 0 ∉ T i) →
    (∀ i x, -x ∈ S i ↔ x ∈ S i) →
    (∀ i x, -x ∈ T i ↔ x ∈ T i) →
    (∀ i x y, y - x ∈ S i ↔ e y - e x ∈ T i) →
    ∃ φ : ZMod 8 ≃+ ZMod 8, ∀ i x, x ∈ S i ↔ φ x ∈ T i

end MathlibPlus.Open.GraphTheory
