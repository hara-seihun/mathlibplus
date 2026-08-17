import Mathlib
import MathlibPlus.Open.NewResearch2.R0033

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372

noncomputable section

/-- The exact positive discrete theta measure in the admitted convolution. -/
def thetaMeasure : Measure ℝ :=
  Measure.sum (fun m : ℤ =>
    ENNReal.ofReal (Real.exp (-Real.pi * (m : ℝ) ^ 2)) •
      Measure.dirac (Real.pi * (m : ℝ) ^ 2))

/-- The Gamma(shape `β`, rate one) measure, including its shape-zero atom. -/
def gammaMeasure (β : ℝ) : Measure ℝ :=
  if β = 0 then
    Measure.dirac (0 : ℝ)
  else
    Measure.withDensity (Measure.restrict volume (Set.Ioi (0 : ℝ)))
      (fun y =>
        ENNReal.ofReal
          (Real.rpow y (β - 1) * Real.exp (-y) / Real.Gamma β))

/-- The binomial Hankel kernel uses the canonical modular-Laguerre `A`. -/
def binomialHankel (α : ℝ) (i j : ℕ) : ℝ :=
  (Nat.choose (i + j) i : ℝ) *
    MathlibPlus.Open.NewResearch2.R0033.laguerreCoefficient α (i + j)

/-- Claim 17371: the binomial Hankel Gram identity. -/
def claim17371 : Prop :=
  ∀ α : ℝ, -((1 : ℝ) / 2) ≤ α →
    ∀ i j : ℕ,
      binomialHankel α i j =
        ∫ x : ℝ, ∫ y : ℝ,
          ((x + y) ^ i / (Nat.factorial i : ℝ)) *
            ((x + y) ^ j / (Nat.factorial j : ℝ))
          ∂(gammaMeasure (α + (1 : ℝ) / 2)) ∂thetaMeasure

/-- Claim 17372: every finite principal binomial-Hankel matrix is
positive semidefinite. -/
def claim17372 : Prop :=
  ∀ α : ℝ, -((1 : ℝ) / 2) ≤ α →
    ∀ N : ℕ,
      Matrix.PosSemidef
        (fun i j : Fin N => binomialHankel α i.1 j.1)

end

end MathlibPlus.Open.ResearchFormalization.R0034Claims17371_17372
