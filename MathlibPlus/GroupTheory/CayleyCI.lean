import Mathlib

namespace MathlibPlus.GroupTheory

/--
The normalized implication from admitted claim 28336 (R-1023): a directed
Cayley-isomorphism witness, when restricted to inverse-closed connection
sets, is an undirected Cayley-isomorphism witness.  The connection-set
predicate is expanded in the theorem type so that no auxiliary CI/DCI
notion is introduced without review.
-/
theorem dci_implies_undirected_ci_claim28336 (G : Type*) [Fintype G] [Group G]
    (hDCI :
      ∀ S T : Set G, ∀ e : G ≃ G,
        (∀ x y : G, y * x⁻¹ ∈ S ↔ e y * (e x)⁻¹ ∈ T) →
          ∃ α : G ≃* G, ∀ x : G, x ∈ S ↔ α x ∈ T) :
    ∀ S T : Set G,
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) →
      (∀ ⦃x : G⦄, x ∈ T → x⁻¹ ∈ T) →
      ∀ e : G ≃ G,
        (∀ x y : G,
          (y * x⁻¹ ∈ S ∨ x * y⁻¹ ∈ S) ↔
            (e y * (e x)⁻¹ ∈ T ∨ e x * (e y)⁻¹ ∈ T)) →
        ∃ α : G ≃* G, ∀ x : G, x ∈ S ↔ α x ∈ T := by
  intro S T hS hT e he
  apply hDCI S T e
  intro x y
  constructor
  · intro hxy
    have hxy' := (he x y).mp (Or.inl hxy)
    rcases hxy' with hdir | hrev
    · exact hdir
    · simpa [mul_inv_rev] using hT hrev
  · intro hxy
    have hxy' := (he x y).mpr (Or.inl hxy)
    rcases hxy' with hdir | hrev
    · exact hdir
    · simpa [mul_inv_rev] using hS hrev

end MathlibPlus.GroupTheory
