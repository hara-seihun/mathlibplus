import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The alternating group on four points is CI for every family of undirected
right-Cayley relation symbols simultaneously. -/
def alternatingFourUndirectedRelationalCI : Prop :=
  ∀ (ι : Type) (S T : ι → Set (alternatingGroup (Fin 4))),
    (∀ i, (1 : alternatingGroup (Fin 4)) ∉ S i) →
    (∀ i, (1 : alternatingGroup (Fin 4)) ∉ T i) →
    (∀ i ⦃x : alternatingGroup (Fin 4)⦄, x ∈ S i → x⁻¹ ∈ S i) →
    (∀ i ⦃x : alternatingGroup (Fin 4)⦄, x ∈ T i → x⁻¹ ∈ T i) →
    ∀ e : alternatingGroup (Fin 4) ≃ alternatingGroup (Fin 4),
      (∀ i x y,
        x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
      ∃ α : alternatingGroup (Fin 4) ≃* alternatingGroup (Fin 4),
        ∀ i x, x ∈ S i ↔ α x ∈ T i

end MathlibPlus.Open.GraphTheory
