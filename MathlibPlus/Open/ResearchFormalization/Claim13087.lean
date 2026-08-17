import MathlibPlus.Open.ResearchFormalization.EndpointPerturbation

namespace MathlibPlus.Open.ResearchFormalization

/-- The strictified family has vanishing endpoint mass and converges to one at
one quarter, while the endpoint counterexample retains all stated scalar
reserves at arbitrarily small positive parameters. -/
def claim13087 : Prop :=
  Filter.Tendsto
      (fun z : ℝ × ℝ => strictifiedEndpointMass z.1 z.2)
      (nhds ((0, 0) : ℝ × ℝ)) (nhds (0 : ℝ)) ∧
    Filter.Tendsto
      (fun z : ℝ × ℝ => strictifiedRealValue z.1 z.2 ((1 : ℝ) / 4))
      (nhds ((0, 0) : ℝ × ℝ)) (nhds (1 : ℝ)) ∧
    ∀ η : ℝ, 0 < η →
      ∃ t : ℝ, 0 < t ∧
        ∀ ε₀ : ℝ, 0 < ε₀ →
          ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧
            let delta : ℝ := strictifiedEndpointMass t ε
            delta = (boundaryCoefficient t 1 + ε) / 4 ∧
              delta < η ∧
              delta ^ 2 + delta < 1 ∧
              strictifiedRealValue t ε ((1 : ℝ) / 4) < 2 ∧
              strictifiedEndpointGap t ε < 0

end MathlibPlus.Open.ResearchFormalization
