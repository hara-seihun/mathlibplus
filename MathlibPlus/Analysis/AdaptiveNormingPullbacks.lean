import Mathlib

namespace MathlibPlus.Analysis

/-- Bounded operators and supplied norming functionals produce the adaptive
continuous-linear pullbacks `φ_j = ℓ_j ∘ T_j`, with the output relation kept
explicit. -/
theorem adaptiveNormingPullbacks
    {𝕜 E Y J : Type*} [NormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : J → E →L[𝕜] Y) (u : J → E) (v : J → Y)
    (ℓ : J → Y →L[𝕜] 𝕜)
    (hv : ∀ j, v j = T j (u j)) :
    ∀ j, ∃ φ : E →L[𝕜] 𝕜,
      φ = (ℓ j).comp (T j) ∧ φ (u j) = ℓ j (v j) := by
  intro j
  refine ⟨(ℓ j).comp (T j), rfl, ?_⟩
  change ℓ j (T j (u j)) = ℓ j (v j)
  rw [hv j]

end MathlibPlus.Analysis
