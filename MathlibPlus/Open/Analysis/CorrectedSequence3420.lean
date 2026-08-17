import MathlibPlus.Open.Analysis.NumeratorInnerOptimizationClaim3422

open scoped BigOperators Topology
open MeasureTheory
open Filter

namespace MathlibPlus.Open.Analysis

noncomputable section

private noncomputable def finiteDirichletPolynomial3420
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ d ∈ S, c d * Complex.exp (-s * (Real.log (d : ℝ) : ℂ))

private noncomputable def finiteDirichletCenter3420
    (S : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  -∑ d ∈ S, c d * (Real.log (d : ℝ) : ℂ) / (d : ℂ)

private noncomputable def finiteDirichletFamily3420
    (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  if s = 1 then finiteDirichletCenter3420 S c
  else finiteDirichletPolynomial3420 S c s * riemannZeta s

private noncomputable def finiteNymanErrorSquared3420
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∫ x in Set.Ioo (0 : ℝ) 1,
    ‖(1 : ℂ) + (1 / finiteDirichletFamily3420 S c 1) *
      (∑ d ∈ S,
        c d * ((Int.fract (1 / ((d : ℝ) * x)) : ℝ) : ℂ))‖ ^ 2

private noncomputable def numeratorBlaschkeMass3420
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  ∑' ρ : {z : ℂ //
      finiteDirichletPolynomial3420 S c z = 0 ∧
        z ≠ 1 ∧ (1 / 2 : ℝ) < z.re},
    (analyticOrderNatAt (finiteDirichletPolynomial3420 S c) ρ.1 : ℝ) *
      Real.log ‖ρ.1 / (1 - ρ.1)‖

private noncomputable def correctedFunctional3420
    (S : Finset ℕ) (c : ℕ → ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + finiteNymanErrorSquared3420 S c) -
    numeratorBlaschkeMass3420 S c

/-- Claim 3420: under RH, the actual finite pole-cancelling Dirichlet
multipliers have Nyman errors tending to zero and their exact corrected
functionals are nonnegative, bounded by the logarithmic norm term, and tend
to zero with that term. -/
def RHsuppliesVanishingCorrectedSequence_claim3420 : Prop :=
  RiemannHypothesis →
    ∃ (S : ℕ → Finset ℕ) (c : ℕ → ℕ → ℂ),
      (∀ n : ℕ,
        finitePoleCancellingDirichletMultiplier (S n) (c n)) ∧
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (finiteNymanErrorSquared3420 (S n) (c n)))
        atTop (𝓝 0) ∧
      (∀ n : ℕ,
        0 ≤ correctedFunctional3420 (S n) (c n) ∧
          correctedFunctional3420 (S n) (c n) ≤
            (1 / 2 : ℝ) *
              Real.log (1 + finiteNymanErrorSquared3420 (S n) (c n))) ∧
      Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) *
            Real.log (1 + finiteNymanErrorSquared3420 (S n) (c n)))
        atTop (𝓝 0)

end

end MathlibPlus.Open.Analysis
