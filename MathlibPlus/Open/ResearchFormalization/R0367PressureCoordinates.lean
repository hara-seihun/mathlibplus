import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0367PressureCoordinates

noncomputable section

def gap (x : ℤ → ℝ) (i : ℤ) : ℝ :=
  x (i + 1) - x i

def pressureTerm (x : ℤ → ℝ) (k j : ℤ) : ℝ :=
  ((x (k + 1) - x j) * (x k - x j))⁻¹

def pressure (x : ℤ → ℝ) (k : ℤ) : ℝ :=
  2 - gap x k ^ 2 *
    ∑' j : {j : ℤ // j ≠ k ∧ j ≠ k + 1}, pressureTerm x k j.1

def leftCoordinate (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (x k - x (k - (r : ℤ))) / gap x k

def rightCoordinate (x : ℤ → ℝ) (k : ℤ) (r : ℕ) : ℝ :=
  (x (k + 1 + (r : ℤ)) - x (k + 1)) / gap x k

def pressureKernel (u : ℝ) : ℝ :=
  1 / (u * (u + 1))

def pressureCoordinateSeries (x : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑' r : ℕ,
    (pressureKernel (leftCoordinate x k (r + 1)) +
      pressureKernel (rightCoordinate x k (r + 1)))

/-- Claim 25646: after the normalized cumulative-distance definitions, the
excluded-index pressure is exactly the left/right kernel series. -/
def claim25646 : Prop :=
  ∀ (x : ℤ → ℝ) (k : ℤ),
    StrictMono x →
      pressure x k = 2 - pressureCoordinateSeries x k

end
end MathlibPlus.Open.ResearchFormalization.R0367PressureCoordinates
