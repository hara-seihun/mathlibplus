import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.R3533WeightedFamily

noncomputable section

open MathlibPlus.Open.Probability.ResearchBatch

/-- Claim 47813: the exact three-atom family uses the reciprocal scalar
parameter and the displayed normalized weights. -/
def weightedFamily_claim47813 : Prop :=
  ∀ q : ℝ, 1 ≤ q →
    let Ω := Cube 3
    let H0 : Ω → ℝ := fun x =>
      match x 0, x 1, x 2 with
      | false, false, false => -1
      | true, false, false => -1
      | false, true, false => -1
      | true, true, false => 1
      | false, false, true => -1
      | true, false, true => 1
      | false, true, true => -1
      | true, true, true => 1
    let H1 : Ω → ℝ := fun x =>
      match x 0, x 1, x 2 with
      | false, false, false => 1
      | true, false, false => -1
      | false, true, false => 1
      | true, true, false => 1
      | false, false, true => -1
      | true, false, true => 1
      | false, true, true => -1
      | true, true, true => 1
    let H2 : Ω → ℝ := fun x =>
      match x 0, x 1, x 2 with
      | false, false, false => 1
      | true, false, false => -1
      | false, true, false => 1
      | true, true, false => 1
      | false, false, true => 1
      | true, false, true => 1
      | false, true, true => -1
      | true, true, true => 1
    let ε : ℝ := q⁻¹
    let weights : Fin 3 → ℝ := ![1 - ε, ε / 2, ε / 2]
    (0 < ε ∧ ε ≤ 1) ∧
      weights 0 = 1 - ε ∧ weights 1 = ε / 2 ∧ weights 2 = ε / 2 ∧
      (∑ i : Fin 3, weights i) = 1 ∧
      (∀ x : Ω, H0 x = -1 ∨ H0 x = 1) ∧
      (∀ x : Ω, H1 x = -1 ∨ H1 x = 1) ∧
      (∀ x : Ω, H2 x = -1 ∨ H2 x = 1)

end

end MathlibPlus.Open.ResearchFormalization.R3533WeightedFamily
