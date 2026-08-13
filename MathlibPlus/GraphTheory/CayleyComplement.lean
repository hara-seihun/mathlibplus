import Lean
import Mathlib

namespace MathlibPlus.GraphTheory.CayleyComplement

open scoped Pointwise

/-- Removing an inverse-closed Cayley connection set from all nonidentity
members produces exactly the graph complement. -/
theorem mulCayley_connectionComplement
    {G : Type*} [Group G] (S : Set G)
    (hSinv : S = S⁻¹) (hSone : 1 ∉ S) :
    SimpleGraph.mulCayley ((Set.univ \ {1}) \ S) =
      (SimpleGraph.mulCayley S)ᶜ := by
  ext x y
  rw [SimpleGraph.compl_adj, SimpleGraph.mulCayley_adj,
    SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    refine ⟨hxy, ?_⟩
    intro hadj
    rcases hmem with hmem | hmem
    · exact hmem.2 (hadj.2.elim id fun hyx => by
        rw [hSinv, Set.mem_inv]
        simpa using hyx)
    · exact hmem.2 (hadj.2.elim (fun hxy' => by
        rw [hSinv, Set.mem_inv]
        simpa using hxy') id)
  · rintro ⟨hxy, hnot⟩
    refine ⟨hxy, Or.inl ⟨?_, ?_⟩⟩
    · simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      exact inv_mul_eq_one.not.mpr hxy
    · intro hmem
      exact hnot ⟨hxy, Or.inl hmem⟩

/-- Complementation preserves the graph-isomorphism quotient of
inverse-closed identity-free Cayley connection sets. -/
theorem nonempty_iso_connectionComplement_iff
    {G : Type*} [Group G] (S T : Set G)
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T) :
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) ↔
      Nonempty
        (SimpleGraph.mulCayley ((Set.univ \ {1}) \ S) ≃g
          SimpleGraph.mulCayley ((Set.univ \ {1}) \ T)) := by
  rw [mulCayley_connectionComplement S hSinv hSone,
    mulCayley_connectionComplement T hTinv hTone]
  constructor
  · rintro ⟨e⟩
    refine ⟨{ toEquiv := e.toEquiv, map_rel_iff' := ?_ }⟩
    intro x y
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    exact and_congr e.injective.ne_iff e.map_rel_iff.not
  · rintro ⟨e⟩
    let ec : (SimpleGraph.mulCayley S)ᶜᶜ ≃g
        (SimpleGraph.mulCayley T)ᶜᶜ :=
      { toEquiv := e.toEquiv
        map_rel_iff' := by
          intro x y
          rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
          exact and_congr e.injective.ne_iff e.map_rel_iff.not }
    exact ⟨by simpa using ec⟩

/-- For each group automorphism, transporting connection sets commutes exactly
with connection-set complementation. This pointwise equivalence preserves the
entire transporter fibre, not merely its nonemptiness. -/
theorem mulEquiv_image_connectionComplement_iff
    {G : Type*} [Group G] (φ : G ≃* G) (S T : Set G)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T) :
    φ '' ((Set.univ \ {1}) \ S) = (Set.univ \ {1}) \ T ↔
      φ '' S = T := by
  constructor
  · intro hcomp
    let A : Set G := Set.univ \ {1}
    have hA : φ '' A = A := by
      dsimp [A]
      rw [Set.image_sdiff φ.injective]
      simp
    have hSsub : S ⊆ A := by
      intro x hx
      simp only [A, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      intro hx1
      exact hSone (hx1 ▸ hx)
    have hTsub : T ⊆ A := by
      intro x hx
      simp only [A, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      intro hx1
      exact hTone (hx1 ▸ hx)
    have hφSsub : φ '' S ⊆ A := by
      rw [← hA]
      exact Set.image_mono hSsub
    have hdiff : A \ (φ '' S) = A \ T := by
      calc
        A \ (φ '' S) = (φ '' A) \ (φ '' S) := by rw [hA]
        _ = φ '' (A \ S) := (Set.image_sdiff φ.injective A S).symm
        _ = A \ T := hcomp
    ext y
    by_cases hyA : y ∈ A
    · have hy := Set.ext_iff.mp hdiff y
      simp only [Set.mem_sdiff, hyA, true_and] at hy
      tauto
    · have hyS : y ∉ φ '' S := fun hy => hyA (hφSsub hy)
      have hyT : y ∉ T := fun hy => hyA (hTsub hy)
      simp [hyS, hyT]
  · intro hφ
    rw [Set.image_sdiff φ.injective, Set.image_sdiff φ.injective, hφ]
    simp

/-- Complementation commutes simultaneously with the graph-isomorphism
quotient and the full group-automorphism transporter fibre. -/
theorem complementPreservesCITransportData
    {G : Type*} [Group G] (S T : Set G)
    (hSinv : S = S⁻¹) (hTinv : T = T⁻¹)
    (hSone : 1 ∉ S) (hTone : 1 ∉ T) :
    (Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) ↔
      Nonempty
        (SimpleGraph.mulCayley ((Set.univ \ {1}) \ S) ≃g
          SimpleGraph.mulCayley ((Set.univ \ {1}) \ T))) ∧
    (∀ φ : G ≃* G,
      (φ '' S = T ↔
        φ '' ((Set.univ \ {1}) \ S) = (Set.univ \ {1}) \ T)) := by
  refine ⟨nonempty_iso_connectionComplement_iff S T hSinv hTinv hSone hTone, ?_⟩
  intro φ
  exact (mulEquiv_image_connectionComplement_iff φ S T hSone hTone).symm

end MathlibPlus.GraphTheory.CayleyComplement
