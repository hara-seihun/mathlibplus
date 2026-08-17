import Mathlib
import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

private noncomputable def finiteInnerCorrectedDirichletPolynomial
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def finiteInnerCorrectedDirichletCenter
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def finiteInnerCorrectedFamily
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finiteInnerCorrectedDirichletCenter S c
  else finiteInnerCorrectedDirichletPolynomial S c s * riemannZeta s

private noncomputable def nymanErrorSquared3414
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / finiteInnerCorrectedFamily S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

private noncomputable def numeratorBlaschkeMass3414
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      finiteInnerCorrectedDirichletPolynomial S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (finiteInnerCorrectedDirichletPolynomial S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def fullyInnerCorrectedFunctional3414
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + nymanErrorSquared3414 S c) -
    numeratorBlaschkeMass3414 S c

private noncomputable def fullyInnerCorrectedFunctionalWithInfinity3414
    (S : Finset ℕ) (c : ℕ → ℂ) (singularInnerMass : ℝ) : ℝ :=
  fullyInnerCorrectedFunctional3414 S c - singularInnerMass

/-- Claim 3414: the actual finite pole-cancelled Dirichlet continuation gives
`R(c) = 1/2 log (1 + d_c^2) - B_A(c)`, while no nonnegative singular-inner
mass at infinity is subtracted; subtracting such a mass can only lower `R(c)`. -/
def fullyInnerCorrectedBSYFunctional_claim3414 : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℂ),
    finitePoleCancellingDirichletMultiplier S c →
      ∀ singularInnerMass : ℝ, 0 ≤ singularInnerMass →
        fullyInnerCorrectedFunctionalWithInfinity3414 S c singularInnerMass ≤
          fullyInnerCorrectedFunctional3414 S c

end

end MathlibPlus.Open.Analysis
