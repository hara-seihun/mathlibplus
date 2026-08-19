import Mathlib
import MathlibPlus.Open.NewResearch2.C0117Concrete
import MathlibPlus.Open.Analysis.LambertWInversionOfV

namespace MathlibPlus.Open.ResearchFormalization.R0125Claim1983

private noncomputable def sourceV (x : ℝ) : ℝ :=
  MathlibPlus.Open.NewResearch2.C0117Concrete.V x

private noncomputable def sourceLambertW (z : ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.principalLambertW z

/-- Claim 1983: with `y = log x` and `z = 2 log y`, the cubed V-expression
is the Lambert equation, and the positive-real principal branch gives the
stated exact inversion. -/
def exactLambertInversion_claim1983 : Prop :=
  ∀ (A x : ℝ), 0 < A → Real.exp 1 < x →
    let y : ℝ := Real.log x
    let z : ℝ := 2 * Real.log y
    sourceV x ^ (3 : ℕ) = y ^ 2 * Real.log y ∧
      y ^ 2 * Real.log y = (1 / 2 : ℝ) * z * Real.exp z ∧
      (sourceV x = A ↔
        Real.log (Real.log x) =
          (1 / 2 : ℝ) * sourceLambertW (2 * A ^ 3))

end MathlibPlus.Open.ResearchFormalization.R0125Claim1983
