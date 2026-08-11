import Mathlib.Analysis.Normed.Module.HahnBanach

namespace MathlibPlus.Analysis

/-- Claim 3949: Hahn--Banach supplies a norming functional over the real or complex scalars. -/
theorem normingFunctionalForTrackedOutput
    (𝕜 : Type*) [RCLike 𝕜]
    (Y : Type*) [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (v : Y) :
    ∃ ℓ : StrongDual 𝕜 Y, ‖ℓ‖ ≤ 1 ∧ ℓ v = ‖v‖ := by
  exact exists_dual_vector'' 𝕜 v

end MathlibPlus.Analysis
