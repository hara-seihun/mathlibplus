import Mathlib

namespace MathlibPlus.GroupTheory.Claim14537

/-!
Formalization of claim 14537's exact logical characterization.  The Cayley
adjacency relation is explicit (`x⁻¹ * y ∈ S`), and `mapsByAut` requires a
bijective multiplicative self-map together with image equality.  No external
CI-group definition is assumed, so the theorem states precisely the
inverse-closed defect equivalence used by the claim.
-/

/-- Failure of the ordinary undirected CI property is equivalent to an
inverse-closed Cayley-graph isomorphism not induced by a group automorphism. -/
theorem inverseClosedDefectCharacterization
    {G : Type*} [Finite G] [Group G] :
    let isConnection : Set G → Prop := fun S ↦
      1 ∉ S ∧ ∀ x ∈ S, x⁻¹ ∈ S
    let cayleyIso : Set G → Set G → Prop := fun S T ↦
      ∃ e : G ≃ G, ∀ x y : G,
        (x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)
    let mapsByAut : Set G → Set G → Prop := fun S T ↦
      ∃ e : G ≃ G,
        (∀ x y : G, e (x * y) = e x * e y) ∧ Set.image e S = T
    let ordinaryCI : Prop := ∀ S T : Set G,
      isConnection S → isConnection T → cayleyIso S T → mapsByAut S T
    (¬ ordinaryCI ↔
      ∃ S T : Set G,
        isConnection S ∧ isConnection T ∧ cayleyIso S T ∧ ¬ mapsByAut S T) := by
  dsimp
  constructor
  · intro h
    push_neg at h
    rcases h with ⟨S, T, hS, hT, hIso, hNoAut⟩
    have hNo : ¬ (∃ e : G ≃ G,
        (∀ x y : G, e (x * y) = e x * e y) ∧ Set.image e S = T) := by
      rintro ⟨e, he, himage⟩
      exact hNoAut e he himage
    exact ⟨S, T, hS, hT, hIso, hNo⟩
  · rintro ⟨S, T, hS, hT, hIso, hNoAut⟩ hCI
    exact hNoAut (hCI S T hS hT hIso)

end MathlibPlus.GroupTheory.Claim14537
