import MathlibPlus.Open.Analysis.ThetaMomentsBatch

namespace MathlibPlus.Open.ResearchFormalization.R3620Claim51017

open MeasureTheory
open scoped BigOperators
open MathlibPlus.Open.Analysis.ThetaMomentsBatch

noncomputable section

/-- The exact Hausdorff moment and finite-difference conclusion on the
verified theta carriers. -/
def thetaAllOrderHausdorffConclusion (μ : Measure ℝ) : Prop :=
  (∀ n : ℕ, 5 ≤ n →
    thetaG n =
      MeasureTheory.integral (μ.restrict (Set.Icc (0 : ℝ) 1))
        (fun q : ℝ => q ^ n)) ∧
    (∀ n r : ℕ, 5 ≤ n → 1 ≤ r →
      ((-1 : ℝ) ^ r) * thetaForwardDifference r thetaFStep n =
        MeasureTheory.integral (μ.restrict (Set.Icc (0 : ℝ) 1))
          (fun q : ℝ => q ^ n * (1 - q) ^ (r - 1)))

def thetaPositiveLaplaceCondition (ν : SignedMeasure NNReal) : Prop :=
  finiteSignedMeasure ν ∧
    thetaLaplaceRepresentation ν ∧ nonnegativeSignedMeasure ν

/-- The exponential reference measure in the factorial/Lambert route. -/
noncomputable def thetaFactorialReferenceMeasure : Measure NNReal :=
  Measure.withDensity nnrealLebesgue
    (fun y : NNReal => ENNReal.ofReal (Real.exp (-(y : ℝ))))

/-- The exact positive Laplace measure and coupled domination condition for
`ell'`, with no free comparison measure. -/
def thetaFactorialCoupledDomination (η : Measure NNReal) : Prop :=
  η ≤ thetaFactorialReferenceMeasure ∧
    ∀ x : ℝ, 5 ≤ x →
      deriv thetaEll x =
        MeasureTheory.integral η
          (fun y : NNReal => Real.exp (-x * (y : ℝ)))

/-- The continuous value at zero of the factorial coupling kernel. -/
noncomputable def thetaFactorialCouplingKernel (y : NNReal) : ℝ :=
  2 * thetaFactorKernel y

/-- The Hausdorff measure coupled to `eta` by the exact factorial route. -/
noncomputable def thetaFactorialCouplingMeasure
    (η : Measure NNReal) : Measure ℝ :=
  Measure.map (fun y : NNReal => Real.exp (-(y : ℝ)))
    (Measure.withDensity (thetaFactorialReferenceMeasure - η)
      (fun y : NNReal =>
        ENNReal.ofReal (thetaFactorialCouplingKernel y)))

/-- The direct factorial/Lambert moment formula before the push-forward. -/
noncomputable def thetaFactorialDirectMoment
    (η : Measure NNReal) (n : ℕ) : ℝ :=
  2 * MeasureTheory.integral (thetaFactorialReferenceMeasure - η)
    (fun y : NNReal =>
      Real.exp (-(n : ℝ) * (y : ℝ)) * thetaFactorKernel y)

/-- The two exact forms of the factorial-route moment, linked to the same
coupling measure. -/
def thetaFactorialMomentEquivalence (η : Measure NNReal) : Prop :=
  ∀ n : ℕ, 5 ≤ n →
    (thetaG n = thetaFactorialDirectMoment η n ↔
      thetaG n =
        MeasureTheory.integral
          ((thetaFactorialCouplingMeasure η).restrict
            (Set.Icc (0 : ℝ) 1))
          (fun q : ℝ => q ^ n))

/-- Claim 51017: either the positive Laplace branch or the exact coupled
factorial branch supplies the complete all-order Hausdorff representation.
Neither branch asserts existence for the theta-specific curvature. -/
def claim51017 : Prop :=
  (∀ ν : SignedMeasure NNReal,
    thetaPositiveLaplaceCondition ν →
      thetaAllOrderHausdorffConclusion (thetaHausdorffMeasure ν)) ∧
    (∀ η : Measure NNReal,
      thetaFactorialCoupledDomination η →
        (∀ n : ℕ, 5 ≤ n →
          thetaG n = thetaFactorialDirectMoment η n) ∧
          thetaFactorialMomentEquivalence η ∧
          thetaAllOrderHausdorffConclusion
            (thetaFactorialCouplingMeasure η))

end

end MathlibPlus.Open.ResearchFormalization.R3620Claim51017
