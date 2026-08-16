import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.CayleyCI

/-- Claim 60208: the cyclic group of order eight is an undirected CI-group. -/
def zmod8_undirected_ci : Prop :=
  ∀ (S T : Set (ZMod 8)),
    S ⊆ (Set.univ \ ({0} : Set (ZMod 8))) →
    T ⊆ (Set.univ \ ({0} : Set (ZMod 8))) →
    (∀ x, x ∈ S → -x ∈ S) →
    (∀ x, x ∈ T → -x ∈ T) →
    (∃ e : Equiv.Perm (ZMod 8),
      (∀ x y, x - y ∈ S ↔ e x - e y ∈ T)) →
    ∃ u : (ZMod 8)ˣ, ∀ x, x ∈ S ↔ (u : ZMod 8) * x ∈ T

end MathlibPlus.Open.FormalizationBatch.CayleyCI
