import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

private noncomputable def finiteDirichletPolynomial_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def finiteDirichletCenter_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def finiteDirichletFamily_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finiteDirichletCenter_claim3418 S c
  else finiteDirichletPolynomial_claim3418 S c s * riemannZeta s

private noncomputable def finiteNymanErrorSquared_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / finiteDirichletFamily_claim3418 S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

private noncomputable def numeratorBlaschkeMass_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      finiteDirichletPolynomial_claim3418 S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (finiteDirichletPolynomial_claim3418 S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def zetaBlaschkeMass_claim3418 : ℝ :=
  ∑' ρ : {z : ℂ //
      z ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def fullyInnerCorrectedFunctional_claim3418
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + finiteNymanErrorSquared_claim3418 S c) -
    numeratorBlaschkeMass_claim3418 S c

private noncomputable def fullyInnerCorrectedInfimum_claim3418 : ℝ :=
  sInf {r : ℝ |
    ∃ (S : Finset ℕ) (c : ℕ → ℂ),
      finitePoleCancellingDirichletMultiplier S c ∧
        r = fullyInnerCorrectedFunctional_claim3418 S c}

/-- Claim 3418: zero corrected infimum forces zero off-line zeta mass and RH. -/
def correctedInfimumCriterion_claim3418 : Prop :=
  fullyInnerCorrectedInfimum_claim3418 = 0 →
    zetaBlaschkeMass_claim3418 = 0 ∧ RiemannHypothesis

end

end MathlibPlus.Open.Analysis
