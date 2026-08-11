import MathlibPlus.Basic

namespace MathlibPlus.Analysis.Claim51591

/-- The exact one-component (`n = 1`) selector calculation from admitted claim 51591.
The three Boolean coordinates are independent uniform signs; the two queried stages
are the private selector and then the shared sign selected by it. -/
theorem selectorTreeN1 :
    let sign : Bool → ℝ := fun b => if b then 1 else -1
    let target : Bool → Bool → Bool → ℝ := fun a yMinus yPlus =>
      if a then sign yPlus else sign yMinus
    let initialVariance : ℝ :=
      (1 / 8 : ℝ) * ∑ a : Bool, ∑ ym : Bool, ∑ yp : Bool,
        (target a ym yp) ^ 2 -
        ((1 / 8 : ℝ) * ∑ a : Bool, ∑ ym : Bool, ∑ yp : Bool,
          target a ym yp) ^ 2
    let selectorConditionalVariance : Bool → ℝ := fun a =>
      (1 / 4 : ℝ) * ∑ ym : Bool, ∑ yp : Bool, (target a ym yp) ^ 2 -
        ((1 / 4 : ℝ) * ∑ ym : Bool, ∑ yp : Bool,
          target a ym yp) ^ 2
    let afterSelector : ℝ :=
      (1 / 2 : ℝ) * ∑ a : Bool, selectorConditionalVariance a
    let selectedConditionalVariance : Bool → Bool → ℝ := fun a y =>
      (1 / 2 : ℝ) * ∑ u : Bool,
          (if a then target a u y else target a y u) ^ 2 -
        ((1 / 2 : ℝ) * ∑ u : Bool,
          if a then target a u y else target a y u) ^ 2
    let afterSelected : ℝ :=
      (1 / 4 : ℝ) * ∑ a : Bool, ∑ y : Bool,
        selectedConditionalVariance a y
    initialVariance = 1 ∧ afterSelector = 1 ∧ afterSelected = 0 ∧
      initialVariance + afterSelector + afterSelected = 2 := by
  dsimp
  norm_num [Fintype.sum_bool]

end MathlibPlus.Analysis.Claim51591
