import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch.Analysis

open scoped BigOperators
open BigOperators
open MeasureTheory

noncomputable section

/-- The two terms in the archimedean Fourier weight. -/
def gaussianWeight (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(5 / 4 : ℝ) * t - Real.pi * (n : ℝ) ^ 2 * Real.exp (-t)) +
    Real.exp ((5 / 4 : ℝ) * t - Real.pi * (n : ℝ) ^ 2 * Real.exp t)

def gaussianDensity (t x : ℝ) : ℝ :=
  Real.exp (-(3 / 4 : ℝ) * t - Real.pi * x ^ 2 * Real.exp t) +
    Real.exp ((3 / 4 : ℝ) * t - Real.pi * x ^ 2 * Real.exp (-t))

/-- Positivity, evenness, and the two Fourier integral representations. -/
def gaussianFourierRepresentation : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (n : ℕ), 0 < n →
    (∀ x : ℝ, 0 < gaussianDensity t x) ∧
    (∀ x : ℝ, gaussianDensity t (-x) = gaussianDensity t x) ∧
    gaussianWeight n t =
      ∫ x : ℝ,
        (gaussianDensity t x : ℂ) *
          Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
            (n : ℂ) * (x : ℂ)) ∧
    gaussianWeight n t =
      2 * MeasureTheory.integral
        (Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ)))
        (fun x => gaussianDensity t x * Real.cos (2 * Real.pi * (n : ℝ) * x))

/-- The folded kernel and its formal iterated q-derivative. -/
def foldedKernel (q ℓ : ℝ) : ℝ :=
  Real.rpow ℓ (-(5 / 4 : ℝ)) * Real.exp (-q / ℓ) +
    Real.rpow ℓ (5 / 4 : ℝ) * Real.exp (-q * ℓ)

def foldedKernelDerivative (q ℓ : ℝ) (m : ℕ) : ℝ :=
  Real.rpow ℓ (-(5 / 4 : ℝ)) * (-1 / ℓ) ^ m * Real.exp (-q / ℓ) +
    Real.rpow ℓ (5 / 4 : ℝ) * (-ℓ) ^ m * Real.exp (-q * ℓ)

def foldedKernelDerivativeFormula : Prop :=
  ∀ (q ℓ : ℝ) (m : ℕ), 0 < ℓ →
    iteratedDeriv m (fun q' : ℝ => foldedKernel q' ℓ) q =
      foldedKernelDerivative q ℓ m

/-- The exact Bellman function and its recurrence for one or more unqueried
    coordinate signs. -/
def bellmanB (s : ℕ) (a : ℤ) : ℚ :=
  (a : ℚ) ^ 2 + ((s * (s + 3) : ℕ) : ℚ) / 2

def bellmanYContinuation (s : ℕ) : ℚ :=
  ((s * (s + 1) : ℕ) : ℚ) / 2

def bellmanXContinuation (s : ℕ) (a : ℤ) : ℚ :=
  (bellmanB (s - 1) (a - 1) + bellmanB (s - 1) (a + 1)) / 2

def bellmanRecurrenceAndSolution : Prop :=
  (∀ a : ℤ, bellmanB 0 a = (a : ℚ) ^ 2) ∧
  (∀ (s : ℕ), 1 ≤ s → ∀ a : ℤ,
    bellmanB s a =
      (a : ℚ) ^ 2 + s + min (bellmanYContinuation s) (bellmanXContinuation s a)) ∧
  (∀ (s : ℕ), 1 ≤ s → ∀ a : ℤ,
    bellmanXContinuation s a = (a : ℚ) ^ 2 + bellmanYContinuation s ∧
    bellmanXContinuation s a = bellmanYContinuation s + (a : ℚ) ^ 2 ∧
    (bellmanXContinuation s a = bellmanYContinuation s ↔ a = 0))

/-- The unweighted theta dilation counterterm at `1` and `2`. -/
def theta (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * (n : ℝ) ^ 2 * t)

def thetaDilationCounterterm : Prop :=
  theta 2 - theta 1 =
      -2 * (∑' n : ℕ,
        (Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2) -
          Real.exp (-2 * Real.pi * ((n + 1 : ℕ) : ℝ) ^ 2))) ∧
    theta 2 - theta 1 < 0 ∧ theta 2 - theta 1 ≠ 0

end
end MathlibPlus.Open.ResearchFormalizationBatch.Analysis
