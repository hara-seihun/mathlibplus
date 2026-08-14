import Mathlib

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.NewResearch2.R0033

noncomputable section

def theta (x : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * (m : ℝ) ^ 2 * x)

def laguerreGeneratingFunction (α t : ℝ) : ℝ :=
  Real.rpow (1 - t) (-α - 1) * theta (1 / (1 - t))

def laguerreCoefficient (α : ℝ) (n : ℕ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    iteratedDeriv n (fun t : ℝ => laguerreGeneratingFunction α t) 0

def risingFactorial (β : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (β + (k : ℝ))

def generalizedBinomial (β : ℝ) (n : ℕ) : ℝ :=
  risingFactorial β n / (Nat.factorial n : ℝ)

def hardEdgeCoefficient (n : ℕ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) *
    ∑' m : ℤ,
      Real.exp (-Real.pi * (m : ℝ) ^ 2) *
        (Real.pi * (m : ℝ) ^ 2) ^ n

def laguerreConvolution (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    generalizedBinomial (α + (1 : ℝ) / 2) k * hardEdgeCoefficient (n - k)

def claim_17358 : Prop :=
  ∀ (α t : ℝ), |t| < 1 →
    (∑' n : ℕ, laguerreCoefficient α n * t ^ n) =
      laguerreGeneratingFunction α t

/-- Jacobi modularity in the exact generating-function form. -/
def claim_17359 : Prop :=
  ∀ (α t : ℝ), |t| < 1 →
    Real.rpow (1 - t) (-α - 1) * theta (1 / (1 - t)) =
      Real.rpow (1 - t) (-α - (1 : ℝ) / 2) * theta (1 - t)

/-- Both coefficient families, and both displayed power-series expansions, are nonnegative. -/
def claim_17360 : Prop :=
  ∀ (α : ℝ), -((1 : ℝ) / 2) ≤ α →
    (∀ n : ℕ, 0 ≤ generalizedBinomial (α + (1 : ℝ) / 2) n ∧
      0 ≤ hardEdgeCoefficient n) ∧
    (∀ t : ℝ, |t| < 1 →
      (∑' n : ℕ, generalizedBinomial (α + (1 : ℝ) / 2) n * t ^ n) =
        Real.rpow (1 - t) (-α - (1 : ℝ) / 2)) ∧
    (∀ t : ℝ, |t| < 1 →
      (∑' n : ℕ, hardEdgeCoefficient n * t ^ n) = theta (1 - t))

/-- Every modular Laguerre coefficient is strictly positive. -/
def claim_17361 : Prop :=
  ∀ (α : ℝ), -((1 : ℝ) / 2) ≤ α →
    ∀ n : ℕ, 0 < laguerreCoefficient α n

/-- The hard-edge coefficient is exactly the theta moment coefficient. -/
def claim_17362 : Prop :=
  ∀ n : ℕ,
    laguerreCoefficient (-(1 : ℝ) / 2) n = hardEdgeCoefficient n ∧
      0 < hardEdgeCoefficient n

/-- Above the hard edge, the coefficient is the positive convolution displayed in the packet. -/
def claim_17363 : Prop :=
  ∀ (α : ℝ), -((1 : ℝ) / 2) < α →
    ∀ n : ℕ,
      laguerreCoefficient α n = laguerreConvolution α n ∧
      (∀ k ∈ Finset.range (n + 1),
        0 ≤ generalizedBinomial (α + (1 : ℝ) / 2) k ∧
          0 ≤ hardEdgeCoefficient (n - k))

end

end MathlibPlus.Open.NewResearch2.R0033
