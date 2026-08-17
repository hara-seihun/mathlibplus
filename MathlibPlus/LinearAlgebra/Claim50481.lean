import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim50481

/-- The augmentation response vanishes exactly when it factors through the
joint source map.  The statement is the linear-algebra core of claim 50481. -/
theorem augmentationFactorization_iff
    {𝕜 C₁ V W Q : Type*} [Field 𝕜]
    [AddCommGroup C₁] [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module 𝕜 C₁] [Module 𝕜 V] [Module 𝕜 W] [Module 𝕜 Q]
    [FiniteDimensional 𝕜 C₁]
    (D : C₁ →ₗ[𝕜] V) (P : C₁ →ₗ[𝕜] W) (A : C₁ →ₗ[𝕜] Q) :
    Submodule.map A (LinearMap.ker D ⊓ LinearMap.ker P) = ⊥ ↔
      ∃ L : V →ₗ[𝕜] Q, ∃ M : W →ₗ[𝕜] Q,
        A = L.comp D + M.comp P := by
  constructor
  · intro hzero
    let J : C₁ →ₗ[𝕜] V × W := D.prod P
    have hker : J.ker ≤ A.ker := by
      rw [show J.ker = LinearMap.ker D ⊓ LinearMap.ker P by
        simp [J, LinearMap.ker_prod]]
      intro x hx
      have hmem : A x ∈ Submodule.map A (LinearMap.ker D ⊓ LinearMap.ker P) :=
        ⟨x, hx, rfl⟩
      rw [hzero] at hmem
      exact (Submodule.mem_bot 𝕜).mp hmem
    let fq : C₁ ⧸ J.ker →ₗ[𝕜] Q := J.ker.liftQ A hker
    let f : J.range →ₗ[𝕜] Q :=
      fq.comp (J.quotKerEquivRange.symm : J.range →ₗ[𝕜] C₁ ⧸ J.ker)
    obtain ⟨F, hF⟩ := LinearMap.exists_extend f
    refine ⟨F.comp (LinearMap.inl 𝕜 V W), F.comp (LinearMap.inr 𝕜 V W), ?_⟩
    ext x
    have hFJ : F (J x) = A x := by
      have h := LinearMap.congr_fun hF ⟨J x, ⟨x, rfl⟩⟩
      have h' : F (J x) = fq (J.quotKerEquivRange.symm ⟨J x, ⟨x, rfl⟩⟩) := by
        simpa [LinearMap.comp_apply, f] using h
      rw [LinearMap.quotKerEquivRange_symm_apply_image J x ⟨x, rfl⟩] at h'
      have hq := LinearMap.congr_fun (Submodule.liftQ_mkQ J.ker A hker) x
      simpa [LinearMap.comp_apply] using h'.trans hq
    calc
      A x = F (J x) := hFJ.symm
      _ = F (D x, P x) := by rfl
      _ = F (D x, 0) + F (0, P x) := by
        rw [show (D x, P x) = (D x, 0) + (0, P x) by simp, map_add]
      _ = (F.comp (LinearMap.inl 𝕜 V W)) (D x) +
          (F.comp (LinearMap.inr 𝕜 V W)) (P x) := by rfl
  · rintro ⟨L, M, hA⟩
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hDx : D x = 0 := LinearMap.mem_ker.mp hx.1
      have hPx : P x = 0 := LinearMap.mem_ker.mp hx.2
      rw [hA]
      simp [LinearMap.comp_apply, hDx, hPx]
    · exact bot_le

/-- The ker-`D` test implies the premise-matched augmentation test; it is
therefore the stronger vanishing condition mentioned in claim 50481. -/
theorem kerD_test_implies_augmentation_test
    {𝕜 C₁ V W Q : Type*} [Field 𝕜]
    [AddCommGroup C₁] [AddCommGroup V] [AddCommGroup W] [AddCommGroup Q]
    [Module 𝕜 C₁] [Module 𝕜 V] [Module 𝕜 W] [Module 𝕜 Q]
    (D : C₁ →ₗ[𝕜] V) (P : C₁ →ₗ[𝕜] W) (A : C₁ →ₗ[𝕜] Q)
    (hD : Submodule.map A (LinearMap.ker D) = ⊥) :
    Submodule.map A (LinearMap.ker D ⊓ LinearMap.ker P) = ⊥ := by
  apply le_antisymm
  · calc
      Submodule.map A (LinearMap.ker D ⊓ LinearMap.ker P) ≤
          Submodule.map A (LinearMap.ker D) :=
        Submodule.map_mono (f := A) inf_le_left
      _ = ⊥ := hD
  · exact bot_le

end MathlibPlus.LinearAlgebra.Claim50481
