import Mathlib

namespace MathlibPlus.Combinatorics

/-!
# Claim 35733: a finite product Cayley connection set

For finite groups `A` and `H`, the source uses the connection set
`{1_A} × (H \ {1_H})`.  The theorem retains the two asserted connection-set
properties and constructs the corresponding simple graph explicitly.
-/

/-- The set `{1_A} × (H \ {1_H})` is identity-free and inverse-closed, and its
left-translation relation gives a simple undirected Cayley graph. -/
theorem claim35733_finiteProductCayleyConnectionSet
    (A H : Type*) [Group A] [Group H] [Fintype A] [Fintype H] :
    let S : Set (A × H) := ({1} : Set A) ×ˢ (Set.univ \ {1})
    ((1 : A × H) ∉ S) ∧
      (∀ s : A × H, s ∈ S → s⁻¹ ∈ S) ∧
      ∃ G : SimpleGraph (A × H),
        ∀ x y, G.Adj x y ↔ x ≠ y ∧ x⁻¹ * y ∈ S := by
  let S : Set (A × H) := ({1} : Set A) ×ˢ (Set.univ \ {1})
  have hone : (1 : A × H) ∉ S := by
    simp [S]
  have hinv : ∀ s : A × H, s ∈ S → s⁻¹ ∈ S := by
    rintro ⟨a, h⟩ hs
    simp only [S, Set.mem_prod, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_univ, Set.mem_singleton_iff] at hs ⊢
    constructor
    · simpa [hs.1]
    · simpa [hs.2]
  let r : (A × H) → (A × H) → Prop := fun x y => x⁻¹ * y ∈ S
  let G : SimpleGraph (A × H) := SimpleGraph.fromRel r
  have hrsymm (x y : A × H) : r y x ↔ r x y := by
    constructor
    · intro h
      have h' := hinv (y⁻¹ * x) h
      simpa [r] using h'
    · intro h
      have h' := hinv (x⁻¹ * y) h
      simpa [r] using h'
  refine ⟨hone, hinv, G, ?_⟩
  intro x y
  change x ≠ y ∧ (r x y ∨ r y x) ↔ x ≠ y ∧ r x y
  rw [show r y x ↔ r x y from hrsymm x y]
  tauto

end MathlibPlus.Combinatorics
