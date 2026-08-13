import Mathlib

namespace MathlibPlus.LinearAlgebra

/-- A uniform scalar weight preserves the rank-one collapse of a finite-dimensional
linear transition map; for a nonzero weight it also preserves the image. -/
theorem fixedMultiplierWeight_preserves_rank_collapse
    {𝕜 V W : Type*} [Field 𝕜] [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W] [FiniteDimensional 𝕜 W]
    (A : V →ₗ[𝕜] W) (w : 𝕜)
    (hA : Module.finrank 𝕜 (LinearMap.range A) ≤ 1) :
    Module.finrank 𝕜 (LinearMap.range (w • A)) ≤ 1 ∧
      (w ≠ 0 →
        LinearMap.range (w • A) = LinearMap.range A ∧
          (Module.finrank 𝕜 (LinearMap.range A) = 1 →
            Module.finrank 𝕜 (LinearMap.range (w • A)) = 1)) := by
  have hle : LinearMap.range (w • A) ≤ LinearMap.range A := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact (LinearMap.range A).smul_mem w ⟨x, rfl⟩
  constructor
  · exact le_trans (Submodule.finrank_mono hle) hA
  · intro hw
    have hrange : LinearMap.range (w • A) = LinearMap.range A := by
      apply le_antisymm
      · exact hle
      · intro y hy
        rcases hy with ⟨x, rfl⟩
        have hmem : w⁻¹ • ((w • A) x) ∈ LinearMap.range (w • A) :=
          (LinearMap.range (w • A)).smul_mem w⁻¹ ⟨x, rfl⟩
        simpa [LinearMap.smul_apply, inv_smul_smul₀ hw] using hmem
    refine ⟨hrange, ?_⟩
    intro hAone
    rw [hrange]
    exact hAone

end MathlibPlus.LinearAlgebra
