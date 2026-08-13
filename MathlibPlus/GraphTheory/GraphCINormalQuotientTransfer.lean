import Mathlib

namespace MathlibPlus.GraphTheory

open scoped Pointwise

/-- Normal-quotient graph-CI heredity reduces to one exact interface: every
ambient automorphism supplied by graph-CI for the pulled-back connection sets
must preserve the chosen normal kernel. The proof separately kernel-checks the
full-preimage graph lift and the quotient descent. -/
theorem graphCIHereditaryToNormalQuotients_of_preimageTransport_preserves :
    ∀ (G : Type*) [Finite G] [Group G]
      (N : Subgroup G) [N.Normal],
      (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
          ∃ φ : G ≃* G, φ '' S = T) →
      (∀ (S T : Set (G ⧸ N)),
        S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
        ∀ φ : G ≃* G,
          φ '' ((QuotientGroup.mk : G → G ⧸ N) ⁻¹' S) =
              (QuotientGroup.mk : G → G ⧸ N) ⁻¹' T →
            N.map φ.toMonoidHom = N) →
      (∀ (S T : Set (G ⧸ N)), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
          ∃ φ : (G ⧸ N) ≃* (G ⧸ N), φ '' S = T) := by
  intro G _ _ N _ hCI hpreserve S T hS_inv hT_inv hS_one hT_one hIso
  let q : G → G ⧸ N := QuotientGroup.mk
  let S' : Set G := q ⁻¹' S
  let T' : Set G := q ⁻¹' T
  have preimage_adj (U : Set (G ⧸ N)) (hU_one : 1 ∉ U) (x y : G) :
      (SimpleGraph.mulCayley (q ⁻¹' U)).Adj x y ↔
        (SimpleGraph.mulCayley U).Adj (q x) (q y) := by
    rw [SimpleGraph.mulCayley_adj, SimpleGraph.mulCayley_adj]
    constructor
    · rintro ⟨hxy, hxyU | hyxU⟩
      · have hdiff : (q x)⁻¹ * q y ∈ U := by
          simpa [q] using hxyU
        refine ⟨?_, Or.inl hdiff⟩
        intro hmk
        apply hU_one
        simpa [hmk] using hdiff
      · have hdiff : (q y)⁻¹ * q x ∈ U := by
          simpa [q] using hyxU
        refine ⟨?_, Or.inr hdiff⟩
        intro hmk
        apply hU_one
        simpa [hmk] using hdiff
    · rintro ⟨hmk, hxyU | hyxU⟩
      · refine ⟨fun hxy => hmk (congrArg q hxy), Or.inl ?_⟩
        simpa [q] using hxyU
      · refine ⟨fun hxy => hmk (congrArg q hxy), Or.inr ?_⟩
        simpa [q] using hyxU
  have hS'_inv : S' = S'⁻¹ := by
    ext x
    change q x ∈ S ↔ q x⁻¹ ∈ S
    rw [show q x⁻¹ = (q x)⁻¹ by simp [q]]
    simpa only [Set.mem_inv] using Set.ext_iff.mp hS_inv (q x)
  have hT'_inv : T' = T'⁻¹ := by
    ext x
    change q x ∈ T ↔ q x⁻¹ ∈ T
    rw [show q x⁻¹ = (q x)⁻¹ by simp [q]]
    simpa only [Set.mem_inv] using Set.ext_iff.mp hT_inv (q x)
  have hS'_one : 1 ∉ S' := by
    simpa [S', q] using hS_one
  have hT'_one : 1 ∉ T' := by
    simpa [T', q] using hT_one
  let f : SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T :=
    Classical.choice hIso
  have fiber_mem (x : G) : (q x).out⁻¹ * x ∈ N := by
    exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (q x))
  let lift : G → G := fun x => (f (q x)).out * ((q x).out⁻¹ * x)
  let unlift : G → G := fun x => (f.symm (q x)).out * ((q x).out⁻¹ * x)
  have lift_mk (x : G) : q (lift x) = f (q x) := by
    change QuotientGroup.mk ((f (q x)).out * ((q x).out⁻¹ * x)) = f (q x)
    rw [QuotientGroup.mk_mul_of_mem _ (fiber_mem x)]
    exact QuotientGroup.out_eq' _
  have unlift_mk (x : G) : q (unlift x) = f.symm (q x) := by
    change QuotientGroup.mk ((f.symm (q x)).out * ((q x).out⁻¹ * x)) = f.symm (q x)
    rw [QuotientGroup.mk_mul_of_mem _ (fiber_mem x)]
    exact QuotientGroup.out_eq' _
  have unlift_lift (x : G) : unlift (lift x) = x := by
    simp [lift, unlift, lift_mk]
  have lift_unlift (x : G) : lift (unlift x) = x := by
    simp [lift, unlift, unlift_mk]
  let liftEquiv : G ≃ G :=
    { toFun := lift
      invFun := unlift
      left_inv := unlift_lift
      right_inv := lift_unlift }
  have hLiftIso :
      Nonempty (SimpleGraph.mulCayley S' ≃g SimpleGraph.mulCayley T') := by
    refine ⟨{ liftEquiv with map_rel_iff' := ?_ }⟩
    intro x y
    rw [preimage_adj T hT_one]
    change (SimpleGraph.mulCayley T).Adj (q (lift x)) (q (lift y)) ↔ _
    rw [lift_mk, lift_mk, f.map_adj_iff]
    exact (preimage_adj S hS_one x y).symm
  obtain ⟨φ, hφ⟩ := hCI S' T' hS'_inv hT'_inv hS'_one hT'_one hLiftIso
  have hN : N.map φ.toMonoidHom = N :=
    hpreserve S T hS_inv hT_inv hS_one hT_one hIso φ hφ
  let ψ : (G ⧸ N) ≃* (G ⧸ N) := QuotientGroup.congr N N φ hN
  have ψ_mk (x : G) : ψ (q x) = q (φ x) := by
    dsimp [ψ, q]
    exact QuotientGroup.congr_mk N N φ hN x
  refine ⟨ψ, Set.Subset.antisymm ?_ ?_⟩
  · rintro z ⟨s, hs, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    rw [ψ_mk]
    have hx : x ∈ S' := hs
    have hφx : φ x ∈ φ '' S' := ⟨x, hx, rfl⟩
    rw [hφ] at hφx
    exact hφx
  · intro t ht
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective t
    have hy : y ∈ T' := ht
    rw [← hφ] at hy
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨q x, hx, ?_⟩
    rw [ψ_mk, hxy]

end MathlibPlus.GraphTheory
