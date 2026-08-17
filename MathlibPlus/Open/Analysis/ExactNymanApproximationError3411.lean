import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.ExactNymanApproximationError3411

noncomputable section

private noncomputable def dirichletPolynomial3411
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def centerValue3411
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def poleCancelledFamily3411
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then centerValue3411 S c
  else dirichletPolynomial3411 S c s * riemannZeta s

private noncomputable def nymanApproximation3411
    (S : Finset ℕ) (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  (1 : ℂ) + (poleCancelledFamily3411 S c 1)⁻¹ *
    ∑ d ∈ S, c d *
      ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ)

private noncomputable def nymanSquaredError3411
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, ‖nymanApproximation3411 S c x‖ ^ 2

private noncomputable def nymanError3411
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (nymanSquaredError3411 S c)

/-- Claim 3411: the exact finite Nyman approximation error is the squared
L² norm of the normalized fractional-part combination, with the center taken
from the pole-cancelled analytic family. -/
def exactNymanApproximationError_claim3411 : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℂ),
    MathlibPlus.Open.Analysis.finitePoleCancellingDirichletMultiplier S c →
      nymanError3411 S c ^ 2 =
        (MeasureTheory.eLpNorm (fun x : ℝ => nymanApproximation3411 S c x)
          2 (volume.restrict (Set.Ioc (0 : ℝ) 1))).toReal ^ 2

end

end MathlibPlus.Open.Analysis.ExactNymanApproximationError3411
