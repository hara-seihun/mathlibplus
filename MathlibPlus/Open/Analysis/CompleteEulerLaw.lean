import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- A real-even smooth source with compact support bounded away from the origin and zero mean. -/
def RealEvenSmoothCompactAnnularZeroMean (f : ℝ → ℝ) : Prop :=
  Function.Even f ∧
    ContDiff ℝ ⊤ f ∧
    (∃ a b : ℝ,
      0 < a ∧ a < b ∧
        ∀ x : ℝ, f x ≠ 0 → a ≤ |x| ∧ |x| ≤ b) ∧
    (∫ x : ℝ, f x) = 0

/-- The centered logarithmic profile used for the Mellin transform. -/
noncomputable def centeredProfile (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (t / 2) * f (Real.exp t)

/-- Mellin transform in the centered logarithmic coordinate. -/
noncomputable def mellinTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ,
    (centeredProfile f t : ℂ) *
      Complex.exp ((s - (1 / 2 : ℂ)) * (t : ℂ))

/-- The completed factor used in the symmetrized source quotient. -/
noncomputable def completedFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ)) *
    Complex.Gamma (s / 2)

/-- The centered completed transform of a source. -/
noncomputable def centeredCompletedTransform (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (mellinTransform f s / completedFactor s +
      mellinTransform f (1 - s) / completedFactor (1 - s))

/-- The exact two-source reduced quotient. -/
noncomputable def reducedTwoSourceQuotient (p q : ℝ → ℝ) (s : ℂ) : ℂ :=
  centeredCompletedTransform p s / centeredCompletedTransform q s

/-- The k-th term of the genuine one-prime Euler logarithmic derivative law. -/
noncomputable def onePrimeEulerTerm (ell k : ℕ) (s : ℂ) : ℂ :=
  (Real.log (ell : ℝ) : ℂ) *
    Complex.exp (-((k : ℂ) * s * (Real.log (ell : ℝ) : ℂ)))

/-- The absolutely convergent one-prime Euler series, indexed by k ≥ 1. -/
noncomputable def onePrimeEulerSeries (ell : ℕ) (s : ℂ) : ℂ :=
  ∑' k : {k : ℕ // 1 ≤ k}, onePrimeEulerTerm ell k.1 s

/-- The complete genuine Euler law at one prime on a right half-plane. -/
def CompleteGenuineOnePrimeEulerLaw (ell : ℕ) (R : ℂ → ℂ) : Prop :=
  ∃ σ : ℝ,
    ∀ s : ℂ, σ < s.re →
      DifferentiableAt ℂ R s ∧
        R s ≠ 0 ∧
        Summable (fun k : {k : ℕ // 1 ≤ k} => ‖onePrimeEulerTerm ell k.1 s‖) ∧
        (-deriv R s / R s = onePrimeEulerSeries ell s)

/-- A quotient is nonconstant when it takes two distinct values. -/
def IsNonconstant (R : ℂ → ℂ) : Prop :=
  ∃ s t : ℂ, R s ≠ R t

/-- No nonconstant exact two-source quotient carries the complete genuine Euler law
at even one isolated prime. -/
def completeGenuineEulerLawAtOnePrimeImpossible : Prop :=
  ∀ (ell : ℕ), Nat.Prime ell →
    ∀ p q : ℝ → ℝ,
      RealEvenSmoothCompactAnnularZeroMean p →
        RealEvenSmoothCompactAnnularZeroMean q →
          ¬ (IsNonconstant (reducedTwoSourceQuotient p q) ∧
            CompleteGenuineOnePrimeEulerLaw
              ell (reducedTwoSourceQuotient p q))

end MathlibPlus.Open.Analysis
