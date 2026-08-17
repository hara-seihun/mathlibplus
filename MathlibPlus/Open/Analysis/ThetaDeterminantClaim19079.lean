import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim19079

noncomputable section

/-- The literal positive-half-line theta source. -/
def literalPhi : ℝ → ℝ := fun u ↦
  ∑' m : {m : ℕ // 0 < m},
    MathlibPlus.Analysis.thetaShellSummand m.1 u

/-- The exact order-five row nodes used in Claims 19078 and 19079. -/
def orderFiveRowNodes : Fin 5 → ℝ :=
  ![(-0.393022564586 : ℝ), (-0.336050274334 : ℝ),
    (-0.291697709339 : ℝ), (-0.202109427346 : ℝ),
    (0.00723065549486 : ℝ)]

/-- The exact order-five column nodes used in Claims 19078 and 19079. -/
def orderFiveColumnNodes : Fin 5 → ℝ :=
  ![(-0.447857389309 : ℝ), (-0.443537823449 : ℝ),
    (-0.225072678420 : ℝ), (-0.0986423714722 : ℝ),
    (-0.0542224093407 : ℝ)]

/-- A certified enclosure records an actual radius below the stated bound. -/
def certifiedEnclosure (value center radiusBound : ℝ) : Prop :=
  ∃ radius : ℝ,
    0 ≤ radius ∧ radius < radiusBound ∧ |value - center| ≤ radius

/-- Claim 19079: at τ = 99/10000 and at the exact supplied nodes, the
heat-weighted order-five determinant is negative with the certified enclosure
stated in the packet. -/
def positiveTimeOrderFiveNegativeDeterminant_claim19079 : Prop :=
  let τ : ℝ := 99 / 10000
  let x : Fin 5 → ℝ := orderFiveRowNodes
  let y : Fin 5 → ℝ := orderFiveColumnNodes
  let D : ℝ :=
    Matrix.det (fun i j : Fin 5 =>
      Real.exp (τ * (x i - y j) ^ 2) * literalPhi |x i - y j|)
  let center : ℝ :=
    -(3.4078550628201097277236057 : ℝ) / (10 : ℝ) ^ 10
  let radiusBound : ℝ := (1.96 : ℝ) / (10 : ℝ) ^ 120
  D < 0 ∧ certifiedEnclosure D center radiusBound

end

end MathlibPlus.Open.Analysis.Claim19079
