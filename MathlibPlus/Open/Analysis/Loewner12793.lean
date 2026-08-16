import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

def counterfeitLoewnerL : ℝ := Real.log 9

def counterfeitHMinus (x : ℝ) : ℝ :=
  (2 * counterfeitLoewnerL *
      Real.sinh (counterfeitLoewnerL * Real.sqrt x)) /
    (Real.sqrt x *
      (2 * Real.cosh (counterfeitLoewnerL * Real.sqrt x) + 7 / 3))

def claim12793 : Prop :=
  ∀ x : ℝ, 0 < x → -deriv counterfeitHMinus x > 0

end MathlibPlus.Open.Analysis
