import MathlibPlus.Open.Analysis.ThetaDeterminantClaim19079

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.R0234Claim19078

noncomputable section

open MathlibPlus.Open.Analysis.Claim19079

def zeroHeatOrderFiveNegativeDeterminant_claim19078 : Prop :=
  let x : Fin 5 → ℝ := orderFiveRowNodes
  let y : Fin 5 → ℝ := orderFiveColumnNodes
  let D : ℝ :=
    Matrix.det (fun i j : Fin 5 => literalPhi |x i - y j|)
  let center : ℝ :=
    -(2.9754349628213787953242671 : ℝ) / (10 : ℝ) ^ 10
  let radiusBound : ℝ := (1.87 : ℝ) / (10 : ℝ) ^ 120
  D < 0 ∧ certifiedEnclosure D center radiusBound

end

end MathlibPlus.Open.Analysis.R0234Claim19078
