import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0085Claim5177

/-- Claim 5177: pointwise degree is recovered from the doubled Euler-curvature
coordinate χ=2-d. -/
def claim5177 : Prop :=
  ∀ {V : Type*} (d χ : V → ℝ),
    (∀ v, χ v = 2 - d v) →
      ∀ v, d v = 2 - χ v

end MathlibPlus.Open.ResearchFormalization.D0085Claim5177
