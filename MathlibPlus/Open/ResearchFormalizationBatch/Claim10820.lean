import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- Claim 10820: atomwise inward Möbius transport with the admitted radial hypotheses. -/
def atomwiseMobiusTransportClaim10820 : Prop :=
  ∀ (r R : ℝ),
    (1 / 2 : ℝ) < r → r < R →
      let u : ℝ := r / R
      let q : ℝ := u ^ 2
      let α : ℝ := (1 - q) / 2
      ∀ (lam : ℝ),
        let zR : ℝ := 2 * R ^ 2 / (R ^ 2 - lam)
        let wR : ℝ := 4 * R ^ 3 / (R ^ 2 - lam) ^ 2
        let zr : ℝ := 2 * r ^ 2 / (r ^ 2 - lam)
        let wr : ℝ := 4 * r ^ 3 / (r ^ 2 - lam) ^ 2
        q * zR / (1 - α * zR) = zr ∧
          u ^ 3 * wR / (1 - α * zR) ^ 2 = wr

end MathlibPlus.Open.ResearchFormalizationBatch
