import MathlibPlus.Open.ResearchFormalization.Claims12988_12990

namespace MathlibPlus.Open.ResearchFormalization.O0131Claim12976

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- Exact squared variables and the meromorphic finite-frequency impedance. -/
def claim12976 : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    (∀ z : ℂ, z ≠ 0 →
      qPlus t z = z - (t : ℂ) ^ 2 / z + 2 * (t : ℂ) * Complex.I ∧
        qMinus t z = z - (t : ℂ) ^ 2 / z - 2 * (t : ℂ) * Complex.I) ∧
      MeromorphicOn (centeredF t) {z : ℂ | z ≠ 0}

end

end MathlibPlus.Open.ResearchFormalization.O0131Claim12976
