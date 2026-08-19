import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.CompactPerturbationClaim3936

open Filter

/-- A weakly-null unit sequence in Hilbert spaces gives the stated lower bound
against every compact perturbation of a fixed bounded operator. -/
def compactPerturbationLowerBound_claim3936 : Prop :=
  ∀ {𝕜 E Y : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y],
    ∀ (u : ℕ → E),
      (∀ φ : StrongDual 𝕜 E,
        Filter.Tendsto (fun j => φ (u j)) Filter.atTop (nhds 0)) →
      (∀ j, ‖u j‖ = 1) →
      ∀ (T : E →L[𝕜] Y),
        ∀ (K : E →L[𝕜] Y),
          IsCompactOperator K →
            ‖T - K‖ ≥ Filter.liminf (fun j => ‖T (u j)‖) Filter.atTop

end MathlibPlus.Open.ResearchFormalization.CompactPerturbationClaim3936
