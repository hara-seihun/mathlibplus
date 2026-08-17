import MathlibPlus.Open.ResearchFormalization.ThetaCorrelation

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 7644: the positive-index theta primitive has the modular and
second-order differential identities on the whole real line. -/
def claim7644_thetaPrimitiveModularDifferentialIdentities : Prop :=
  (∀ t : ℝ, thetaG (-t) = thetaG t + Real.sinh (t / 2)) ∧
    ∀ t : ℝ,
      deriv (fun s : ℝ => deriv thetaG s) t -
          (1 / 4 : ℝ) * thetaG t =
        thetaPhi t

end MathlibPlus.Open.ResearchFormalization
