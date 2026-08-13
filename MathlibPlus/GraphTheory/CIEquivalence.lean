import Batteries
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace MathlibPlus.GraphTheory

open scoped Pointwise

/-- A group automorphism carrying one connection set onto another induces an
isomorphism of the corresponding multiplicative Cayley graphs. -/
theorem exists_mulCayley_iso_of_aut_image {G : Type*} [Group G] (φ : G ≃* G)
    (S T : Set G) (hST : φ '' S = T) :
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) := by
  refine ⟨{
    __ := φ.toEquiv
    map_rel_iff' := ?_
  }⟩
  intro u v
  have hmem (x : G) : φ x ∈ T ↔ x ∈ S := by
    rw [← hST]
    simp
  rw [SimpleGraph.mulCayley_adj, SimpleGraph.mulCayley_adj]
  change (φ u ≠ φ v ∧ ((φ u)⁻¹ * φ v ∈ T ∨ (φ v)⁻¹ * φ u ∈ T)) ↔
    (u ≠ v ∧ (u⁻¹ * v ∈ S ∨ v⁻¹ * u ∈ S))
  have hmul₁ : (φ u)⁻¹ * φ v = φ (u⁻¹ * v) := by simp
  have hmul₂ : (φ v)⁻¹ * φ u = φ (v⁻¹ * u) := by simp
  rw [hmul₁, hmul₂, hmem, hmem]
  exact and_congr φ.injective.eq_iff.not Iff.rfl

/-- The universal undirected graph-CI implication is equivalent to equality of
its graph-isomorphism fibres and group-automorphism orbits on every pair of
admissible connection sets. -/
theorem graphCI_iff_orbitFibers_eq {G : Type*} [Finite G] [Group G] :
    (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : G ≃* G, φ '' S = T) ↔
    (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      (Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) ↔
        ∃ φ : G ≃* G, φ '' S = T)) := by
  constructor
  · intro hCI S T hSinv hTinv hSone hTone
    constructor
    · exact hCI S T hSinv hTinv hSone hTone
    · rintro ⟨φ, hφ⟩
      exact exists_mulCayley_iso_of_aut_image φ S T hφ
  · intro h S T hSinv hTinv hSone hTone hIso
    exact (h S T hSinv hTinv hSone hTone).mp hIso

/-- The universal undirected graph-CI implication is equivalently the absence
of an admissible isomorphic pair separated by every group automorphism. -/
theorem graphCI_iff_noDefect {G : Type*} [Finite G] [Group G] :
    (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∃ φ : G ≃* G, φ '' S = T) ↔
    ¬ ∃ S T : Set G,
      S = S⁻¹ ∧ T = T⁻¹ ∧ 1 ∉ S ∧ 1 ∉ T ∧
      Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) ∧
      ∀ φ : G ≃* G, φ '' S ≠ T := by
  constructor
  · intro hCI ⟨S, T, hSinv, hTinv, hSone, hTone, hIso, hsep⟩
    obtain ⟨φ, hφ⟩ := hCI S T hSinv hTinv hSone hTone hIso
    exact hsep φ hφ
  · intro hnone S T hSinv hTinv hSone hTone hIso
    by_contra hnot
    apply hnone
    refine ⟨S, T, hSinv, hTinv, hSone, hTone, hIso, ?_⟩
    simpa only [not_exists] using hnot

end MathlibPlus.GraphTheory
