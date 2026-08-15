import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.ArithmeticKernels

def oneEndpointCosineTransform_claim2300 (L z : ℝ) (K : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, K x * Real.cos (z * (x - L / 2))

def finiteArithmeticKernel_claim2306 (c : ℕ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt (c : ℝ) *
    ∑ n ∈ (Finset.range c).filter (fun n : ℕ =>
      (n : ℝ) < (c : ℝ) * Real.exp (-x)),
      Polynomial.eval ((n : ℝ) * Real.exp x / (c : ℝ)) p

def finiteArithmeticKernel (c : ℕ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  finiteArithmeticKernel_claim2306 c p x

def finiteArithmeticKernel_claim2369 (c : ℕ) (p : Polynomial ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) / Real.sqrt (c : ℝ) *
    ∑ n ∈ (Finset.range c).filter (fun n : ℕ =>
      (n : ℝ) < (c : ℝ) * Real.exp (-x)),
      Polynomial.eval ((n : ℝ) * Real.exp x / (c : ℝ)) p

def arithmeticJumpFormula_claim2307 : Prop :=
  ∀ c : ℕ, ∀ p : Polynomial ℝ, ∀ n : ℕ,
    1 ≤ n → n < c →
    let x₀ := Real.log c - Real.log n
    let leftValue :=
      Real.exp (x₀ / 2) / Real.sqrt (c : ℝ) *
        ∑ m ∈ (Finset.range c).filter (fun m : ℕ => 1 ≤ m ∧ m ≤ n),
          Polynomial.eval ((m : ℝ) * Real.exp x₀ / (c : ℝ)) p
    let rightValue :=
      Real.exp (x₀ / 2) / Real.sqrt (c : ℝ) *
        ∑ m ∈ (Finset.range c).filter (fun m : ℕ => 1 ≤ m ∧ m < n),
          Polynomial.eval ((m : ℝ) * Real.exp x₀ / (c : ℝ)) p
    Filter.Tendsto (finiteArithmeticKernel c p)
        (nhdsWithin x₀ (Set.Iio x₀)) (nhds leftValue) ∧
    Filter.Tendsto (finiteArithmeticKernel c p)
        (nhdsWithin x₀ (Set.Ioi x₀)) (nhds rightValue) ∧
    leftValue - rightValue = Polynomial.eval 1 p / Real.sqrt n

end MathlibPlus.Open.ResearchBatch.ArithmeticKernels
