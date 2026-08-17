import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

private noncomputable def finiteDirichletPolynomial
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def finiteDirichletCenter
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

/-- The pole-cancelled analytic continuation attached to the actual finite
Dirichlet polynomial and its removable center value. -/
private noncomputable def finiteDirichletFamily
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finiteDirichletCenter S c
  else finiteDirichletPolynomial S c s * riemannZeta s

/-- The Nyman--Beurling squared error for the same finite multiplier. -/
private noncomputable def finiteNymanErrorSquared
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / finiteDirichletFamily S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

/-- The complete numerator Blaschke mass, using the analytic order of the
actual finite Dirichlet polynomial at each of its half-plane zeros. -/
private noncomputable def numeratorBlaschkeMass
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      finiteDirichletPolynomial S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (finiteDirichletPolynomial S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

/-- The off-critical-line zeta Blaschke mass, with the actual analytic order
of each zeta zero. -/
private noncomputable def zetaBlaschkeMass : ℝ :=
  ∑' ρ : {z : ℂ //
      z ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

/-- The fully inner-corrected functional, with no singular inner mass at
infinity subtracted. -/
private noncomputable def fullyInnerCorrectedFunctional
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + finiteNymanErrorSquared S c) -
    numeratorBlaschkeMass S c

/-- The unrestricted infimum over finite pole-cancelling multipliers with a
nonzero center. -/
private noncomputable def fullyInnerCorrectedInfimum : ℝ :=
  sInf {r : ℝ |
    ∃ (S : Finset ℕ) (c : ℕ → ℂ),
      finitePoleCancellingDirichletMultiplier S c ∧
        r = fullyInnerCorrectedFunctional S c}

/-- Claim 3422: minimizing the fully inner-corrected numerator functional
over all finite pole-cancelling Dirichlet multipliers reaches zero exactly
when the Riemann hypothesis holds. -/
def numeratorInnerOptimizationNotSofter_claim3422 : Prop :=
  fullyInnerCorrectedInfimum = 0 ↔ RiemannHypothesis

end

end MathlibPlus.Open.Analysis
