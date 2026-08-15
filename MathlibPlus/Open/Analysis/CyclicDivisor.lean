import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- Evaluation of a real polynomial at a complex point. -/
def complexPolynomialEval (P : Polynomial ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℝ ℂ) z P

/-- The exponential coordinate `m ^ (1/2 - s)` of a cyclic quotient. -/
def cyclicCoordinate (m : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((1 / 2 - s) * Complex.ofReal (Real.log m))

/-- The asserted lift of a nonzero finite divisor point. -/
def cyclicDivisorLift (m : ℝ) (α : ℂ) (k : ℤ) : ℂ :=
  (1 / 2 : ℂ) -
      Complex.ofReal (Real.log ‖α‖) / Complex.ofReal (Real.log m) -
      Complex.I *
        Complex.ofReal (Complex.arg α + 2 * Real.pi * (k : ℝ)) /
          Complex.ofReal (Real.log m)

/-- The nonzero finite divisor points of the reduced rational function `U/V`. -/
def finiteDivisorPoints (U V : Polynomial ℝ) : Set ℂ :=
  {α | α ≠ 0 ∧
    (complexPolynomialEval U α = 0 ∨ complexPolynomialEval V α = 0)}

/-- The global zero-and-pole divisor of the cyclic quotient `U/V`. -/
def cyclicDivisor (m : ℝ) (U V : Polynomial ℝ) : Set ℂ :=
  {s |
    complexPolynomialEval U (cyclicCoordinate m s) = 0 ∨
      complexPolynomialEval V (cyclicCoordinate m s) = 0}

/-- One vertical arithmetic progression in the `s`-plane. -/
def verticalDivisorProgression (m : ℝ) (α : ℂ) : Set ℂ :=
  Set.range (cyclicDivisorLift m α)

/-- Constancy of the rational function represented by the reduced pair `U,V`. -/
def cyclicQuotientIsConstant (U V : Polynomial ℝ) : Prop :=
  ∃ c : ℂ, ∀ x : ℂ,
    complexPolynomialEval U x = c * complexPolynomialEval V x

/--
Divisor points of a cyclic quotient lift periodically under `x = m^(1/2-s)`;
the resulting global divisor is an infinite finite union of vertical arithmetic
progressions for every nonconstant quotient, and a finite global divisor forces
constancy.
-/
def divisorOfCyclicQuotientIsPeriodic : Prop :=
  ∀ (m : ℝ) (U V : Polynomial ℝ),
    1 < m →
    IsCoprime U V →
    complexPolynomialEval U 0 ≠ 0 →
    complexPolynomialEval V 0 ≠ 0 →
    (∀ (α : ℂ), α ∈ finiteDivisorPoints U V →
      ∀ k : ℤ, cyclicDivisorLift m α k ∈ cyclicDivisor m U V) ∧
    (¬ cyclicQuotientIsConstant U V →
      Set.Infinite (cyclicDivisor m U V) ∧
      Set.Finite (finiteDivisorPoints U V) ∧
      cyclicDivisor m U V =
        ⋃ α ∈ finiteDivisorPoints U V, verticalDivisorProgression m α) ∧
    (Set.Finite (cyclicDivisor m U V) → cyclicQuotientIsConstant U V)

end MathlibPlus.Open.Analysis
