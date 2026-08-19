import MathlibPlus.Open.Probability.ResearchBatch

namespace MathlibPlus.Open.ResearchFormalization.R3533TargetExpectedArea

noncomputable section

open MathlibPlus.Open.Probability.ResearchBatch

/-- Claim 47817: the explicitly checked Bellman policy gives the exact target
area and the expected component-area comparison for every admissible epsilon. -/
def targetExpectedArea_claim47817 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
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
    let target : Ω → ℝ := fun x =>
      (1 - ε) * H0 x + (ε / 2) * H1 x + (ε / 2) * H2 x
    let policy : QueryTree 3 :=
      .node 0
        (.node 2 (.node 1 .leaf .leaf) (.node 1 .leaf .leaf))
        (.node 2 (.node 1 .leaf .leaf) (.node 1 .leaf .leaf))
    let targetArea : ℝ :=
      25 / 16 - 15 * ε / 16 + 73 * ε ^ 2 / 64
    let expectedArea : ℝ := 25 / 16 + 15 * ε / 32
    valid policy ∧
      complete target policy ∧
      policyArea target policy = targetArea ∧
      optimalArea target = targetArea ∧
      (1 - ε) * optimalArea H0 +
          (ε / 2) * optimalArea H1 +
          (ε / 2) * optimalArea H2 = expectedArea ∧
      expectedArea - targetArea = 45 * ε / 32 - 73 * ε ^ 2 / 64 ∧
      expectedArea - targetArea > 0

end

end MathlibPlus.Open.ResearchFormalization.R3533TargetExpectedArea
