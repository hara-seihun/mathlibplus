import Mathlib
import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.NymanBeurling3419

noncomputable section

private noncomputable def dirichletPolynomial
    (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ d ∈ s, c d * Complex.exp (-z * (Real.log (d : ℝ) : ℂ))

private noncomputable def dirichletCenter
    (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ s, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def poleCancelledFamily
    (s : Finset ℕ) (c : ℕ → ℂ) (z : ℂ) : ℂ :=
  if z = 1 then dirichletCenter s c else
    dirichletPolynomial s c z * riemannZeta z

private noncomputable def nymanErrorSquared
    (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1,
    ‖(1 : ℂ) + (poleCancelledFamily s c 1)⁻¹ *
      ∑ d ∈ s, c d *
        ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ)‖ ^ 2

private noncomputable def nymanError
    (s : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  Real.sqrt (nymanErrorSquared s c)

/-- Claim 3419: the exact Nyman--Beurling criterion, with the infimum over
finite pole-cancelling multipliers and the analytic-continuation value at one
used in the Nyman error. -/
def nymanBeurlingCriterion_claim3419 : Prop :=
  RiemannHypothesis ↔
    sInf {r : ℝ |
      ∃ (s : Finset ℕ) (c : ℕ → ℂ),
        MathlibPlus.Open.Analysis.finitePoleCancellingDirichletMultiplier s c ∧
          r = nymanError s c} = 0

end

end MathlibPlus.Open.Analysis.NymanBeurling3419
