import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0070Claim4956

/-- Claim 4956: independently nonzero-rescaling selected columns preserves
both the selected span and its finite rank. -/
def claim4956 : Prop :=
  ∀ {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (v : ι → V) (w : ι → 𝕜),
    (∀ i, w i ≠ 0) →
      ∀ S : Finset ι,
        let U : Submodule 𝕜 V :=
          Submodule.span 𝕜 (v '' (S : Set ι))
        let U' : Submodule 𝕜 V :=
          Submodule.span 𝕜 ((fun i => w i • v i) '' (S : Set ι))
        U' = U ∧ Module.finrank 𝕜 U' = Module.finrank 𝕜 U

end MathlibPlus.Open.ResearchFormalization.D0070Claim4956
