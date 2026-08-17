import Mathlib
import MathlibPlus.Open.Analysis.Claim3410DirichletMultiplier

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Analysis

noncomputable section

private noncomputable def correctedDirichletPolynomial
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def correctedDirichletCenter
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def correctedDirichletFamily
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then correctedDirichletCenter S c
  else correctedDirichletPolynomial S c s * riemannZeta s

private noncomputable def correctedNymanErrorSquared
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / correctedDirichletFamily S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

private noncomputable def correctedNumeratorBlaschkeMass
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      correctedDirichletPolynomial S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (correctedDirichletPolynomial S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def correctedZetaBlaschkeMass : ℝ :=
  ∑' ρ : {z : ℂ //
      z ∈ riemannZetaZeros ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def correctedFunctionalR
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + correctedNymanErrorSquared S c) -
    correctedNumeratorBlaschkeMass S c

def universalCorrectedFunctionalLowerBound_claim3416 : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℂ),
    finitePoleCancellingDirichletMultiplier S c →
      correctedFunctionalR S c ≥ correctedZetaBlaschkeMass ∧
        correctedZetaBlaschkeMass ≥ 0

end
end MathlibPlus.Open.Analysis
