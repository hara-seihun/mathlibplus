import Batteries
import MathlibPlus.Open.GraphTheory.GraphCIQuotient

namespace MathlibPlus.GraphTheory.LeftTranslationStabilizer

open scoped Pointwise

/-- Left translation of a full quotient preimage is the full preimage of the
left-translated quotient set. -/
theorem smul_quotientPreimage
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Set (G ⧸ N)) (g : G) :
    g • ((QuotientGroup.mk' N) ⁻¹' S) =
      (QuotientGroup.mk' N) ⁻¹' ((QuotientGroup.mk' N g) • S) := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change QuotientGroup.mk' N (g⁻¹ * y) ∈ S ↔
    QuotientGroup.mk' N y ∈ (QuotientGroup.mk' N g) • S
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp

/-- The left-translation stabilizer of a full quotient preimage is exactly the
comap of the left-translation stabilizer downstairs. -/
theorem stabilizer_quotientPreimage
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Set (G ⧸ N)) :
    MulAction.stabilizer G ((QuotientGroup.mk' N) ⁻¹' S) =
      (MulAction.stabilizer (G ⧸ N) S).comap (QuotientGroup.mk' N) := by
  ext g
  change
    g • ((QuotientGroup.mk' N) ⁻¹' S) =
        (QuotientGroup.mk' N) ⁻¹' S ↔
      (QuotientGroup.mk' N g) • S = S
  rw [smul_quotientPreimage]
  exact (QuotientGroup.mk'_surjective N).preimage_injective.eq_iff

/-- If the quotient set has trivial left-translation stabilizer, its full
preimage canonically recovers the chosen normal kernel as its stabilizer. -/
theorem stabilizer_quotientPreimage_eq_kernel
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Set (G ⧸ N)) (hS : MulAction.stabilizer (G ⧸ N) S = ⊥) :
    MulAction.stabilizer G ((QuotientGroup.mk' N) ⁻¹' S) = N := by
  rw [stabilizer_quotientPreimage, hS]
  change (QuotientGroup.mk' N).ker = N
  exact QuotientGroup.ker_mk' N

/-- Left-translation stabilizers are functorial under group equivalences. -/
theorem stabilizer_image_mulEquiv
    {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (S : Set G) :
    MulAction.stabilizer H (e '' S) =
      (MulAction.stabilizer G S).map (e : G →* H) := by
  ext h
  constructor
  · intro hh
    refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    change e.symm h • S = S
    change h • (e '' S) = e '' S at hh
    have himage : e '' (e.symm h • S) = e '' S := by
      rw [Set.image_smul_distrib]
      simpa using hh
    exact e.injective.image_injective himage
  · rintro ⟨g, hg, rfl⟩
    change e g • (e '' S) = e '' S
    rw [← Set.image_smul_distrib]
    exact congrArg (fun U : Set G => e '' U) hg

/-- An automorphism transporting full preimages of two left-aperiodic quotient
sets must stabilize the chosen normal kernel. -/
theorem map_eq_of_trivialStabilizer_quotientPreimage_transport
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (e : G ≃* G) (S T : Set (G ⧸ N))
    (hS : MulAction.stabilizer (G ⧸ N) S = ⊥)
    (hT : MulAction.stabilizer (G ⧸ N) T = ⊥)
    (he : e '' ((QuotientGroup.mk' N) ⁻¹' S) =
      (QuotientGroup.mk' N) ⁻¹' T) :
    N.map (e : G →* G) = N := by
  have hstabilizer := stabilizer_image_mulEquiv e
    ((QuotientGroup.mk' N) ⁻¹' S)
  rw [he, stabilizer_quotientPreimage_eq_kernel N S hS,
    stabilizer_quotientPreimage_eq_kernel N T hT] at hstabilizer
  exact hstabilizer.symm

/-- A kernel-stabilizing group automorphism commutes, on sets, with pullback
along the quotient map. -/
theorem image_quotientPreimage_eq_quotientPreimage_image
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (e : G ≃* G) (hN : N.map (e : G →* G) = N)
    (S : Set (G ⧸ N)) :
    e '' ((QuotientGroup.mk' N) ⁻¹' S) =
      (QuotientGroup.mk' N) ⁻¹'
        ((QuotientGroup.congr N N e hN) '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change QuotientGroup.mk' N (e x) ∈
      (QuotientGroup.congr N N e hN) '' S
    refine ⟨QuotientGroup.mk' N x, hx, ?_⟩
    rfl
  · intro hy
    change QuotientGroup.mk' N y ∈
      (QuotientGroup.congr N N e hN) '' S at hy
    rcases hy with ⟨z, hz, hzy⟩
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change QuotientGroup.mk' N (e.symm y) ∈ S
    have heq : QuotientGroup.mk' N (e.symm y) = z := by
      apply (QuotientGroup.congr N N e hN).injective
      change QuotientGroup.mk' N (e (e.symm y)) =
        (QuotientGroup.congr N N e hN) z
      rw [e.apply_symm_apply]
      exact hzy.symm
    rw [heq]
    exact hz

/-- Exact quotient/full-preimage transport equivalence for a
kernel-stabilizing automorphism. -/
theorem quotientImage_eq_iff_preimageImage_eq
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (e : G ≃* G) (hN : N.map (e : G →* G) = N)
    (S T : Set (G ⧸ N)) :
    (QuotientGroup.congr N N e hN) '' S = T ↔
      e '' ((QuotientGroup.mk' N) ⁻¹' S) =
        (QuotientGroup.mk' N) ⁻¹' T := by
  constructor
  · intro hST
    rw [image_quotientPreimage_eq_quotientPreimage_image N e hN S, hST]
  · intro hpre
    rw [image_quotientPreimage_eq_quotientPreimage_image N e hN S] at hpre
    ext z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact Set.ext_iff.mp hpre x

/-- Graph-CI descends through an arbitrary finite normal quotient for pairs of
connection sets with trivial left-translation stabilizer.  No characteristic
kernel hypothesis is used: aperiodicity canonically recovers the kernel from
each pulled-back connection set. -/
theorem graphCIHereditaryToNormalQuotients_of_trivialStabilizer :
    ∀ (G : Type*) [Finite G] [Group G] (N : Subgroup G) [N.Normal],
      (∀ (S T : Set G), S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
          ∃ φ : G ≃* G, φ '' S = T) →
      ∀ (S T : Set (G ⧸ N)),
        S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
        MulAction.stabilizer (G ⧸ N) S = ⊥ →
        MulAction.stabilizer (G ⧸ N) T = ⊥ →
        Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
          ∃ φ : (G ⧸ N) ≃* (G ⧸ N), φ '' S = T := by
  intro G _ _ N _ hCI S T hS_inv hT_inv hS_one hT_one hS_stab hT_stab hIso
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
  have hφ' : φ '' ((QuotientGroup.mk' N) ⁻¹' S) =
      (QuotientGroup.mk' N) ⁻¹' T := by
    simpa [S', T', q] using hφ
  have hN : N.map (φ : G →* G) = N :=
    map_eq_of_trivialStabilizer_quotientPreimage_transport
      N φ S T hS_stab hT_stab hφ'
  refine ⟨QuotientGroup.congr N N φ hN, ?_⟩
  exact (quotientImage_eq_iff_preimageImage_eq N φ hN S T).2 hφ'

end MathlibPlus.GraphTheory.LeftTranslationStabilizer
