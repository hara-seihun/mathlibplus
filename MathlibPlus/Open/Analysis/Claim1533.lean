import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.Open.Analysis

/-!
Claim 1533 (Bellotti exponential-sum ceilings).  Decimal inputs are exact
Lean rationals.  Fractional powers use `Real.rpow`, and the two displayed
headrooms are included rather than silently reducing the claim to the two
upper bounds.
-/

/-- The exact two ceiling inequalities and their directed headrooms. -/
def bellottiExponentialSumCeilings_1533 : Prop :=
  let C : ℝ := 8.7979
  let D : ℝ := 132.94357
  let A : ℝ :=
    (C + 1 + (10 : ℝ) ^ (-80 : ℤ)) /
        (108 * Real.log 10) ^ (2 / 3 : ℝ) +
      1.569 * C * D ^ (1 / 3 : ℝ)
  let B : ℝ := (2 / 9 : ℝ) * Real.sqrt (3 * D)
  A < 70.699401 ∧
    B < 4.4379437 ∧
    70.699401 - A > 8.2153306673 * (10 : ℝ) ^ (-7 : ℤ) ∧
    4.4379437 - B > 6.5420612543 * (10 : ℝ) ^ (-8 : ℤ)

end MathlibPlus.Open.Analysis
