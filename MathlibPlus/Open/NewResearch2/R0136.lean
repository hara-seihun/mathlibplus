import Mathlib

noncomputable section

namespace MathlibPlus.Open.NewResearch2.R0136

/-- Claim 18194: in the affine first-activity setting, the gap debt pays the
exact tangent-line identity. -/
def claim18194_correctedAffineGapDebtIdentity : Prop :=
  ∀ (P N : ℝ → ℝ → ℝ) (h1 h2 h3 : ℝ),
    (∃ p0 p1 n0 n1 : ℝ,
      (∀ z : ℝ, P z h3 = p0 + p1 * z) ∧
      (∀ z : ℝ, N z h3 = n0 + n1 * z)) →
      let D : ℝ := P h2 h3 - h2 * N h2 h3
      let B : ℝ := deriv (fun z : ℝ => P z h3) h1 -
        h2 * deriv (fun z : ℝ => N z h3) h1
      P h1 h3 - h2 * N h1 h3 = D + (h1 - h2) * B

end MathlibPlus.Open.NewResearch2.R0136
