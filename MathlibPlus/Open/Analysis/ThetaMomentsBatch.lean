import Mathlib

open scoped BigOperators
open MeasureTheory
open ProbabilityTheory

namespace MathlibPlus.Open.Analysis.ThetaMomentsBatch

noncomputable def nnrealLebesgue : Measure NNReal :=
  Measure.map Real.toNNReal
    (MeasureTheory.volume.restrict (Set.Ici (0 : ℝ)))

noncomputable def thetaT (u : ℝ) : ℝ :=
  ∑' m : ℕ, if 1 ≤ m then
    Real.exp (-Real.pi * (m : ℝ) ^ 2 * Real.exp (2 * u))
  else 0

noncomputable def thetaI (x : ℝ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    Real.exp (u / 2) * thetaT u * Real.rpow u (2 * x)

noncomputable def thetaMoment (x : ℝ) : ℝ :=
  2 * thetaI x / Real.Gamma (2 * x + 1)

noncomputable def thetaF (x : ℝ) : ℝ := Real.log (thetaMoment x)

noncomputable def thetaFStep (n : ℕ) : ℝ :=
  thetaF ((n + 1 : ℕ) : ℝ) - thetaF (n : ℝ)

noncomputable def thetaG (n : ℕ) : ℝ :=
  2 * thetaF ((n + 1 : ℕ) : ℝ) - thetaF (n : ℝ) -
    thetaF ((n + 2 : ℕ) : ℝ)

noncomputable def thetaH (x : ℝ) : ℝ :=
  -deriv (deriv thetaF) x

noncomputable def thetaTiltedMeasure (x : ℝ) : Measure ℝ :=
  Measure.withDensity (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun u => ENNReal.ofReal
      (Real.exp (u / 2) * thetaT u * Real.rpow u (2 * x) / thetaI x))

noncomputable def thetaTrigamma (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

noncomputable def thetaTiltedVariance (x : ℝ) : ℝ :=
  ProbabilityTheory.variance (fun u : ℝ => Real.log u)
    (thetaTiltedMeasure x)

/-- The tilted-cumulant identities, including the probability normalization. -/
def tiltedCumulantCurvatureIdentity : Prop :=
  ∀ x : ℝ, 5 ≤ x →
    IsProbabilityMeasure (thetaTiltedMeasure x) ∧
    deriv thetaI x / thetaI x =
      2 * MeasureTheory.integral (thetaTiltedMeasure x)
        (fun u : ℝ => Real.log u) ∧
    deriv (deriv thetaI) x / thetaI x =
      4 * MeasureTheory.integral (thetaTiltedMeasure x)
        (fun u : ℝ => (Real.log u) ^ 2) ∧
    thetaH x = 4 * (thetaTrigamma (2 * x + 1) - thetaTiltedVariance x)

noncomputable def thetaSignedIntegral
    (ν : SignedMeasure NNReal) (f : NNReal → ℝ) : ℝ :=
  MeasureTheory.integral ν.toJordanDecomposition.posPart f -
    MeasureTheory.integral ν.toJordanDecomposition.negPart f

def finiteSignedMeasure (ν : SignedMeasure NNReal) : Prop :=
  IsFiniteMeasure ν.toJordanDecomposition.posPart ∧
    IsFiniteMeasure ν.toJordanDecomposition.negPart

def thetaLaplaceRepresentation (ν : SignedMeasure NNReal) : Prop :=
  ∀ x : ℝ, 5 ≤ x →
    thetaH x = thetaSignedIntegral ν
      (fun y : NNReal => Real.exp (-x * (y : ℝ)))

noncomputable def thetaKernel0 (y : NNReal) : ℝ :=
  if y = 0 then 1 else
    (1 - Real.exp (-(y : ℝ))) ^ 2 / (y : ℝ) ^ 2

noncomputable def thetaBridgeKernel (n : ℕ) (y : NNReal) : ℝ :=
  if y = 0 then 1 else
    Real.exp (-(n : ℝ) * (y : ℝ)) *
      (1 - Real.exp (-(y : ℝ))) ^ 2 / (y : ℝ) ^ 2

noncomputable def thetaDoubleIntegral (n : ℕ) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) 1,
    ∫ t in Set.Icc (0 : ℝ) 1, thetaH ((n : ℝ) + s + t)

def nonnegativeSignedMeasure (ν : SignedMeasure NNReal) : Prop :=
  ν.toJordanDecomposition.negPart = 0

noncomputable def thetaHausdorffMeasure (ν : SignedMeasure NNReal) : Measure ℝ :=
  Measure.map (fun y : NNReal => Real.exp (-(y : ℝ)))
    (Measure.withDensity ν.toJordanDecomposition.posPart
      (fun y => ENNReal.ofReal (thetaKernel0 y)))

def thetaForwardDifference : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, n => f n
  | r + 1, f, n =>
      thetaForwardDifference r (fun k => f (k + 1) - f k) n

/-- The Laplace bridge and its positive push-forward consequence. -/
def laplaceBridgeAndHausdorffPushForward : Prop :=
  ∀ (ν : SignedMeasure NNReal), finiteSignedMeasure ν →
    thetaLaplaceRepresentation ν →
    (∀ n : ℕ, 5 ≤ n →
      thetaG n = thetaDoubleIntegral n ∧
      thetaG n = thetaSignedIntegral ν (thetaBridgeKernel n)) ∧
    (nonnegativeSignedMeasure ν →
      (∀ n : ℕ, 5 ≤ n →
        thetaG n = MeasureTheory.integral
          ((thetaHausdorffMeasure ν).restrict (Set.Icc (0 : ℝ) 1))
          (fun q : ℝ => q ^ n)) ∧
      (∀ n r : ℕ, 5 ≤ n → 1 ≤ r →
        ((-1 : ℝ) ^ r) * thetaForwardDifference r thetaFStep n =
          MeasureTheory.integral
            ((thetaHausdorffMeasure ν).restrict (Set.Icc (0 : ℝ) 1))
            (fun q : ℝ => q ^ n * (1 - q) ^ (r - 1))) ∧
      (∀ n r : ℕ, 5 ≤ n → 1 ≤ r →
        0 < (thetaHausdorffMeasure ν) (Set.Ioo (0 : ℝ) 1) →
        0 < MeasureTheory.integral
          ((thetaHausdorffMeasure ν).restrict (Set.Icc (0 : ℝ) 1))
          (fun q : ℝ => q ^ n * (1 - q) ^ (r - 1))))

noncomputable def thetaEll (x : ℝ) : ℝ :=
  Real.log (4 * (x + 1) *
    Real.sqrt (thetaMoment (x + 1) / thetaMoment x))

noncomputable def thetaEllStep (n : ℕ) : ℝ :=
  thetaEll ((n + 1 : ℕ) : ℝ) - thetaEll (n : ℝ)

noncomputable def thetaFactorKernel (y : NNReal) : ℝ :=
  if y = 0 then 1 else
    (1 - Real.exp (-(y : ℝ))) / (y : ℝ)

/-- The curvature formula fixes the comparison measure in the coupling. -/
def curvatureDeterminesComparisonMeasure : Prop :=
  ∀ x : ℝ, 5 ≤ x →
    deriv thetaEll x =
      1 / (x + 1) -
        (1 / 2) * (∫ s in Set.Icc x (x + 1), thetaH s) ∧
    ∀ ν : SignedMeasure NNReal, finiteSignedMeasure ν →
      thetaLaplaceRepresentation ν →
      deriv thetaEll x =
        (MeasureTheory.integral nnrealLebesgue
          (fun y : NNReal =>
            Real.exp (-x * (y : ℝ)) * Real.exp (-(y : ℝ)))) -
        (1 / 2) * thetaSignedIntegral ν
          (fun y : NNReal =>
            Real.exp (-x * (y : ℝ)) * thetaFactorKernel y)

end MathlibPlus.Open.Analysis.ThetaMomentsBatch
