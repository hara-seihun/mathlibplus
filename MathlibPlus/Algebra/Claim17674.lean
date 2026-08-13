import Mathlib

namespace MathlibPlus.Algebra.Claim17674

/-- The edge contribution for ordered levels `r,s` in claim 17674. -/
def edgeContribution (d_r d_s θ_r θ_s : ℝ) : ℝ :=
  d_r * d_s * (θ_r - θ_s)

@[simp] theorem edgeContribution_eq (d_r d_s θ_r θ_s : ℝ) :
    edgeContribution d_r d_s θ_r θ_s = d_r * d_s * (θ_r - θ_s) := rfl

end MathlibPlus.Algebra.Claim17674
