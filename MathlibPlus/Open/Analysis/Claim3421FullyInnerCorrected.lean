import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis.Claim3421

noncomputable section

private noncomputable def finiteDirichletPolynomial
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def finiteDirichletCenter
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def finiteDirichletFamily
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finiteDirichletCenter S c
  else finiteDirichletPolynomial S c s * riemannZeta s

private noncomputable def finiteNymanErrorSquared
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / finiteDirichletFamily S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

private noncomputable def numeratorBlaschkeMass
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      finiteDirichletPolynomial S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (finiteDirichletPolynomial S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def zetaBlaschkeMass : ℝ :=
  ∑' ρ : {z : ℂ //
      z ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def fullyInnerCorrectedFunctional
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + finiteNymanErrorSquared S c) -
    numeratorBlaschkeMass S c

private noncomputable def fullyInnerCorrectedInfimum : ℝ :=
  sInf {r : ℝ |
    ∃ (S : Finset ℕ) (c : ℕ → ℂ),
      finitePoleCancellingDirichletMultiplier S c ∧
        r = fullyInnerCorrectedFunctional S c}

/-- Claim 3421: the fully inner-corrected functional has infimum zero over
all admissible finite pole-cancelling multipliers exactly when RH holds. -/
def exactFullyInnerCorrectedRHCriterion_claim3421 : Prop :=
  RiemannHypothesis ↔ fullyInnerCorrectedInfimum = 0

end

end MathlibPlus.Open.Analysis.Claim3421
