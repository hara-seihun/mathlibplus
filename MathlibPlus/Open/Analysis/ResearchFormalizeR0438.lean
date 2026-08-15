import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators
open Filter

noncomputable section

/-- The consecutive gap of a bi-infinite real sequence. -/
def gap (x : ℤ → ℝ) (i : ℤ) : ℝ :=
  x (i + 1) - x i

/-- The summand in the adjacent-collision pressure series. -/
def pressureTerm (x : ℤ → ℝ) (k j : ℤ) : ℝ :=
  ((x (k + 1) - x j) * (x k - x j))⁻¹

/-- The pressure at an adjacent pair, with the two adjacent indices removed. -/
def pressure (x : ℤ → ℝ) (k : ℤ) : ℝ :=
  2 - gap x k ^ 2 *
    ∑' j : {j : ℤ // j ≠ k ∧ j ≠ k + 1}, pressureTerm x k j.1

/-- Absolute convergence of the pressure series at one adjacent pair. -/
def AbsolutelyConvergentPressure (x : ℤ → ℝ) (k : ℤ) : Prop :=
  Summable (fun j : {j : ℤ // j ≠ k ∧ j ≠ k + 1} =>
    ‖pressureTerm x k j.1‖)

/-- The normalized left and right coordinates used in the pressure profile. -/
def leftCoordinate (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (x k - x (k - (r : ℤ))) / gap x k

def rightCoordinate (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (x (k + 1 + (r : ℤ)) - x (k + 1)) / gap x k

/-- The finite gap-sum expressions for the two normalized coordinates. -/
def leftCoordinateSum (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, gap x (k - (j : ℤ)) / gap x k

def rightCoordinateSum (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 r, gap x (k + (j : ℤ)) / gap x k

/-- The positive kernel in pressure coordinates. -/
def pressureCoordinateKernel (u : ℝ) : ℝ :=
  1 / (u * (u + 1))

def pressureCoordinateSeries (x : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑' r : ℕ,
    (pressureCoordinateKernel (leftCoordinate x k (r + 1)) +
      pressureCoordinateKernel (rightCoordinate x k (r + 1)))

def finitePressureCoordinateSum (x : ℤ → ℝ) (k : ℤ) (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    (pressureCoordinateKernel (leftCoordinate x k r) +
      pressureCoordinateKernel (rightCoordinate x k r))

/-- The normalized cumulative symmetric gap profile. -/
def symmetricGapProfile (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 r,
    (gap x (k - (j : ℤ)) + gap x (k + (j : ℤ)) - 2 * gap x k)) /
    gap x k

/-- The scalar bound appearing in the curvature estimate. -/
def scalarCurvatureBound (R : ℕ) (μ : ℝ) : ℝ :=
  2 / ((R : ℝ) + 1) +
    (μ / 6) * (R : ℝ) * (4 * (R : ℝ) + 5) / ((R : ℝ) + 1)

/-- Claim 21364: adjacent collision pressure and normalized coordinates. -/
def adjacentCollisionPressureNormalizedCoordinates : Prop :=
  ∀ (x : ℤ → ℝ), StrictMono x →
    ∀ (k : ℤ) (r : ℕ), 1 ≤ r →
      leftCoordinate x k r = leftCoordinateSum x k r ∧
        rightCoordinate x k r = rightCoordinateSum x k r

/-- Claim 21365: exact pressure-coordinate identity and finite truncation bounds. -/
def exactPressureCoordinateIdentity : Prop :=
  ∀ (x : ℤ → ℝ) (k : ℤ), StrictMono x →
    AbsolutelyConvergentPressure x k →
      pressure x k = 2 - pressureCoordinateSeries x k ∧
        (∀ r : ℕ, 1 ≤ r →
          0 < pressureCoordinateKernel (leftCoordinate x k r) ∧
            0 < pressureCoordinateKernel (rightCoordinate x k r)) ∧
        (∀ R : ℕ, 1 ≤ R →
          pressure x k ≤ 2 - finitePressureCoordinateSum x k R)

/-- Claim 21367: cumulative symmetric gap-profile pressure bound. -/
def cumulativeSymmetricGapProfilePressureBound : Prop :=
  ∀ (x : ℤ → ℝ) (k : ℤ) (R : ℕ) (E : ℕ → ℝ),
    StrictMono x →
    Tendsto x atTop atTop →
    Tendsto x atBot atBot →
    AbsolutelyConvergentPressure x k →
    (∀ r : ℕ, r ∈ Finset.Icc 1 R →
      symmetricGapProfile x k r ≤ E r ∧
        0 < (r : ℝ) + E r / 2) →
    pressure x k ≤
      2 - 2 * ∑ r ∈ Finset.Icc 1 R,
        pressureCoordinateKernel ((r : ℝ) + E r / 2)

/-- Claim 21368: exact left-right affine-drift cancellation. -/
def exactLeftRightAffineDriftCancellation : Prop :=
  ∀ (x : ℤ → ℝ), StrictMono x →
    ∀ (k : ℤ) (r : ℕ), 1 ≤ r →
      leftCoordinate x k r + rightCoordinate x k r =
        2 * (r : ℝ) + symmetricGapProfile x k r

/-- Claim 21369: scalar curvature pressure bound. -/
def scalarCurvaturePressureBound : Prop :=
  ∀ (x : ℤ → ℝ) (k : ℤ) (R : ℕ) (μ : ℝ),
    StrictMono x →
    1 ≤ R →
    0 ≤ μ →
    (∀ j : ℕ, j ∈ Finset.Icc 1 R →
      gap x (k - (j : ℤ)) + gap x (k + (j : ℤ)) - 2 * gap x k ≤
        μ * gap x k * (j : ℝ) ^ 2) →
    pressure x k ≤ scalarCurvatureBound R μ

end

end MathlibPlus.Open.Analysis
