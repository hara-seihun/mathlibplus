import MathlibPlus.Algebra.TranslationPeriod

namespace MathlibPlus.Algebra.TranslationPeriod

noncomputable section

variable {B C : Type*} [AddCommGroup B] [AddCommGroup C]

/-- Translation commutes with transport by an additive equivalence. -/
theorem translateSet_image_addEquiv
    (e : B ≃+ C) (X : Set B) (u : B) :
    translateSet (e '' X) (e u) = e '' translateSet X u := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x + u, ⟨x, hx, rfl⟩, ?_⟩
    exact map_add e x u
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    exact (map_add e x u).symm

/-- The full translation-period subgroup is functorial under additive
 equivalences. -/
theorem periodSubgroup_image_addEquiv
    (e : B ≃+ C) (X : Set B) :
    periodSubgroup (e '' X) = (periodSubgroup X).map (e : B →+ C) := by
  ext v
  constructor
  · intro hv
    refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
    change translateSet X (e.symm v) = X
    change translateSet (e '' X) v = e '' X at hv
    have himage : e '' translateSet X (e.symm v) = e '' X := by
      rw [← translateSet_image_addEquiv]
      simpa using hv
    exact e.injective.image_injective himage
  · rintro ⟨u, hu, rfl⟩
    change translateSet (e '' X) (e u) = e '' X
    rw [translateSet_image_addEquiv, hu]

/-- Translation of a full quotient preimage is the full preimage of the
translated quotient set. -/
theorem translateSet_quotientPreimage
    (N : AddSubgroup B) (S : Set (B ⧸ N)) (u : B) :
    translateSet ((QuotientAddGroup.mk' N) ⁻¹' S) u =
      (QuotientAddGroup.mk' N) ⁻¹'
        (translateSet S (QuotientAddGroup.mk' N u)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨QuotientAddGroup.mk' N x, hx, ?_⟩
    exact (map_add (QuotientAddGroup.mk' N) x u).symm
  · rintro ⟨z, hz, hzy⟩
    refine ⟨y - u, ?_, by simp⟩
    change QuotientAddGroup.mk' N (y - u) ∈ S
    rw [map_sub, ← hzy]
    simpa using hz

/-- The period subgroup of a full quotient preimage is exactly the comap of the
period subgroup downstairs. -/
theorem periodSubgroup_quotientPreimage
    (N : AddSubgroup B) (S : Set (B ⧸ N)) :
    periodSubgroup ((QuotientAddGroup.mk' N) ⁻¹' S) =
      (periodSubgroup S).comap (QuotientAddGroup.mk' N) := by
  ext u
  change
    translateSet ((QuotientAddGroup.mk' N) ⁻¹' S) u =
        (QuotientAddGroup.mk' N) ⁻¹' S ↔
      translateSet S (QuotientAddGroup.mk' N u) = S
  rw [translateSet_quotientPreimage]
  exact (QuotientAddGroup.mk'_surjective N).preimage_injective.eq_iff

/-- An aperiodic quotient set makes the quotient kernel exactly recoverable as
the translation-period subgroup of its full preimage. -/
theorem periodSubgroup_quotientPreimage_eq_kernel
    (N : AddSubgroup B) (S : Set (B ⧸ N))
    (hS : periodSubgroup S = ⊥) :
    periodSubgroup ((QuotientAddGroup.mk' N) ⁻¹' S) = N := by
  rw [periodSubgroup_quotientPreimage, hS]
  change (QuotientAddGroup.mk' N).ker = N
  exact QuotientAddGroup.ker_mk' N

/-- If an additive automorphism transports full preimages of two aperiodic
quotient sets, it must stabilize the chosen quotient kernel. -/
theorem map_eq_of_aperiodic_quotientPreimage_transport
    (N : AddSubgroup B) (e : B ≃+ B) (S T : Set (B ⧸ N))
    (hS : periodSubgroup S = ⊥) (hT : periodSubgroup T = ⊥)
    (he : e '' ((QuotientAddGroup.mk' N) ⁻¹' S) =
      (QuotientAddGroup.mk' N) ⁻¹' T) :
    N.map (e : B →+ B) = N := by
  have hperiod := periodSubgroup_image_addEquiv e
    ((QuotientAddGroup.mk' N) ⁻¹' S)
  rw [he, periodSubgroup_quotientPreimage_eq_kernel N S hS,
    periodSubgroup_quotientPreimage_eq_kernel N T hT] at hperiod
  exact hperiod.symm

/-- A kernel-stabilizing additive automorphism commutes, on sets, with pullback
along the quotient map. -/
theorem image_quotientPreimage_eq_quotientPreimage_image
    (N : AddSubgroup B) (e : B ≃+ B)
    (hN : N.map (e : B →+ B) = N) (S : Set (B ⧸ N)) :
    e '' ((QuotientAddGroup.mk' N) ⁻¹' S) =
      (QuotientAddGroup.mk' N) ⁻¹'
        ((QuotientAddGroup.congr N N e hN) '' S) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change QuotientAddGroup.mk' N (e x) ∈
      (QuotientAddGroup.congr N N e hN) '' S
    refine ⟨QuotientAddGroup.mk' N x, hx, ?_⟩
    rfl
  · intro hy
    change QuotientAddGroup.mk' N y ∈
      (QuotientAddGroup.congr N N e hN) '' S at hy
    rcases hy with ⟨z, hz, hzy⟩
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change QuotientAddGroup.mk' N (e.symm y) ∈ S
    have heq : QuotientAddGroup.mk' N (e.symm y) = z := by
      apply (QuotientAddGroup.congr N N e hN).injective
      change QuotientAddGroup.mk' N (e (e.symm y)) =
        (QuotientAddGroup.congr N N e hN) z
      rw [e.apply_symm_apply]
      exact hzy.symm
    rw [heq]
    exact hz

/-- Exact set-transport equivalence for a kernel-stabilizing additive
automorphism. -/
theorem quotientImage_eq_iff_preimageImage_eq
    (N : AddSubgroup B) (e : B ≃+ B)
    (hN : N.map (e : B →+ B) = N) (S T : Set (B ⧸ N)) :
    (QuotientAddGroup.congr N N e hN) '' S = T ↔
      e '' ((QuotientAddGroup.mk' N) ⁻¹' S) =
        (QuotientAddGroup.mk' N) ⁻¹' T := by
  constructor
  · intro hST
    rw [image_quotientPreimage_eq_quotientPreimage_image N e hN S, hST]
  · intro hpre
    rw [image_quotientPreimage_eq_quotientPreimage_image N e hN S] at hpre
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective N z
    exact Set.ext_iff.mp hpre x

/-- Full-preimage transport between aperiodic quotient sets always descends to
an additive automorphism of the quotient. -/
theorem exists_quotientAddEquiv_of_aperiodic_preimage_transport
    (N : AddSubgroup B) (e : B ≃+ B) (S T : Set (B ⧸ N))
    (hS : periodSubgroup S = ⊥) (hT : periodSubgroup T = ⊥)
    (he : e '' ((QuotientAddGroup.mk' N) ⁻¹' S) =
      (QuotientAddGroup.mk' N) ⁻¹' T) :
    ∃ f : (B ⧸ N) ≃+ (B ⧸ N), f '' S = T := by
  have hN : N.map (e : B →+ B) = N :=
    map_eq_of_aperiodic_quotientPreimage_transport N e S T hS hT he
  refine ⟨QuotientAddGroup.congr N N e hN, ?_⟩
  exact (quotientImage_eq_iff_preimageImage_eq N e hN S T).2 he

end

end MathlibPlus.Algebra.TranslationPeriod
