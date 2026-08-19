import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.R3533ComponentAreas

noncomputable section

open MathlibPlus.Open.Probability.ResearchBatch

/-- Claim 47815: the exact three Boolean atoms have the displayed optimal
posterior-variance areas. -/
def componentAreas_claim47815 : Prop :=
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
  optimalArea H0 = 25 / 16 ∧
    optimalArea H1 = 33 / 16 ∧
    optimalArea H2 = 2

end

end MathlibPlus.Open.ResearchFormalization.R3533ComponentAreas
