import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.R3533DisplayedRatios

noncomputable section

open MathlibPlus.Open.Probability.ResearchBatch

/-- Claim 47821: the exact q-dependent target ratio, with the checked
Bellman policy and posterior-area semantics, has the two displayed values. -/
def displayedRatios_claim47821 : Prop :=
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
  let policy : QueryTree 3 :=
    .node 0
      (.node 2 (.node 1 .leaf .leaf) (.node 1 .leaf .leaf))
      (.node 2 (.node 1 .leaf .leaf) (.node 1 .leaf .leaf))
  let ratio : ℝ → ℝ := fun q =>
    let ε : ℝ := q⁻¹
    let target : Ω → ℝ := fun x =>
      (1 - ε) * H0 x + (ε / 2) * H1 x + (ε / 2) * H2 x
    let expectedArea : ℝ :=
      (1 - ε) * optimalArea H0 +
        (ε / 2) * optimalArea H1 +
        (ε / 2) * optimalArea H2
    optimalArea target / expectedArea
  valid policy ∧
    (ratio 1024 = (104796233 : ℝ) / 104888320 ∧
      ratio 1024 < 1) ∧
    (ratio 65536 = (429492797513 : ℝ) / 429498695680 ∧
      ratio 65536 < 1)

end

end MathlibPlus.Open.ResearchFormalization.R3533DisplayedRatios
