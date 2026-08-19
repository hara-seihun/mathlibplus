import Mathlib
import MathlibPlus.Open.ResearchFormalization.R1156Claim31657_31660

namespace MathlibPlus.Open.ResearchFormalization.R1156DerivativeReparam

open MathlibPlus.Open.ResearchFormalization.R1156

noncomputable section

/-- The doubling reparametrization on `F₇`. -/
def doubling_claim41420 : F7 → F7 :=
  fun w => (2 : F7) * w

/-- Replacing the derivative variable `s` by `2w` preserves exactly the
relative-derivative signature for every one of the reviewed nonlinear labels. -/
def claim41420 : Prop :=
  Function.Bijective doubling_claim41420 ∧
    ∀ (δ : F7 → F7),
      nonlinearNormalizedLabel δ →
        ∀ r : F7,
          Set.range ((relativeDerivative δ r) ∘ doubling_claim41420) =
            Set.range (relativeDerivative δ r)

end
end MathlibPlus.Open.ResearchFormalization.R1156DerivativeReparam
