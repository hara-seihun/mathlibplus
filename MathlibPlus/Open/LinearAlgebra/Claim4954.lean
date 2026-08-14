import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.Claim4954

/-- A column presentation may be changed by an ambient linear equivalence,
reindexed by an equivalence of ground sets, and independently scaled by
weights on the original columns. -/
def coordinate_reindex_projective
    {𝕜 : Type*} [Field 𝕜]
    {ι κ V W : Type*}
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (columns : ι → V) (transformed : κ → W) : Prop :=
  ∃ (e : V ≃ₗ[𝕜] W) (σ : κ ≃ ι) (w : ι → 𝕜),
    ∀ j, transformed j = w (σ j) • e (columns (σ j))

end MathlibPlus.Open.LinearAlgebra.Claim4954
