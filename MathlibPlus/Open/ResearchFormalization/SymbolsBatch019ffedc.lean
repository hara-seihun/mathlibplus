import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open scoped BigOperators

noncomputable section

def partialZetaOmega (n : ℕ) : ℝ :=
  2 * Real.pi * (1 / 2 - Real.log (n : ℝ) / Real.log 8)

def partialZetaWeight (n : ℕ) : ℝ := Real.rpow (n : ℝ) (-1 / 2 : ℝ)

def partialZetaSymbol (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) * Complex.sin ((Real.pi : ℂ) * z) +
    Finset.sum (Finset.Icc (1 : ℕ) 7)
      (fun n => (partialZetaWeight n : ℂ) *
        Complex.sin ((partialZetaOmega n : ℂ) * z))

/-- Claim 2210. -/
def partialZetaJumpFrequenciesAndSymbol : Prop :=
  (∀ n : ℕ, 1 ≤ n → n ≤ 7 →
    partialZetaOmega n =
      2 * Real.pi * (1 / 2 - Real.log (n : ℝ) / Real.log 8)) ∧
  (∀ r : ℝ, ∀ z : ℂ,
    partialZetaSymbol r z =
      (r : ℂ) * Complex.sin ((Real.pi : ℂ) * z) +
        Finset.sum (Finset.Icc (1 : ℕ) 7)
          (fun n => (Real.rpow (n : ℝ) (-1 / 2 : ℝ) : ℂ) *
            Complex.sin ((partialZetaOmega n : ℂ) * z)))

/-- Claim 2211. -/
def realSimpleZerosForAllLargeCoefficients : Prop :=
  ∀ r : ℝ, (2 : ℝ) / 3 ≤ r →
    ∀ z : ℂ, partialZetaSymbol r z = 0 →
      z.im = 0 ∧ deriv (partialZetaSymbol r) z ≠ 0

def residualB (x y₃ y₅ : ℝ) : ℝ :=
  Real.sin (3 * x) +
    (Real.rpow 2 (-1 / 2 : ℝ) - 1 / 2) * Real.sin x +
    Real.rpow 3 (-1 / 2 : ℝ) * Real.sin (3 * x - y₃) +
    Real.rpow 5 (-1 / 2 : ℝ) * Real.sin (3 * x - y₅) +
    Real.rpow 6 (-1 / 2 : ℝ) * Real.sin (x - y₃)

def residualC (x y₃ y₅ : ℝ) : ℝ :=
  Real.pi * Real.cos (3 * x) +
    Real.pi / 3 * (Real.rpow 2 (-1 / 2 : ℝ) - 1 / 2) * Real.cos x +
    Real.rpow 3 (-1 / 2 : ℝ) * partialZetaOmega 3 *
      Real.cos (3 * x - y₃) +
    Real.rpow 5 (-1 / 2 : ℝ) * partialZetaOmega 5 *
      Real.cos (3 * x - y₅) +
    Real.rpow 6 (-1 / 2 : ℝ) * partialZetaOmega 6 *
      Real.cos (x - y₃)

def residualA (r x y₃ y₅ : ℝ) : ℝ :=
  residualB x y₃ y₅ + r * Real.sin (3 * x)

def residualD (r x y₃ y₅ : ℝ) : ℝ :=
  residualC x y₃ y₅ + r * Real.pi * Real.cos (3 * x)

def residualQ (r x y₃ y₅ : ℝ) : ℝ :=
  7 * (residualA r x y₃ y₅)^2 +
    7 * (residualD r x y₃ y₅)^2 / (partialZetaOmega 7)^2

/-- Claim 2215, with all real phase representatives of the complete torus. -/
def certifiedTorusGapAtTwoThirds : Prop :=
  ∀ x y₃ y₅ : ℝ,
    residualQ (2 / 3) x y₃ y₅ > 1.0003237125904446992 ∧
    deriv (fun r : ℝ => residualQ r x y₃ y₅) (2 / 3) >
      0.0036594301115362599

def shiftedLogCounterfeitOmega (n : ℕ) : ℝ :=
  if n = 1 then Real.pi else
    2 * Real.pi *
      (1 / 2 - Real.log ((n : ℝ) + 37 / 100) / Real.log (837 / 100))

def shiftedLogCounterfeitSymbol (z : ℂ) : ℂ :=
  ((2 / 3 : ℝ) : ℂ) * Complex.sin ((Real.pi : ℂ) * z) +
    Finset.sum (Finset.Icc (1 : ℕ) 7)
      (fun n => (partialZetaWeight n : ℂ) *
        Complex.sin ((shiftedLogCounterfeitOmega n : ℂ) * z))

def shiftedLogCounterfeitCenter : ℂ :=
  (23.4320451646867296138484604827444485 : ℝ) +
    (0.1487832491328836961630701727259944 : ℝ) * Complex.I

/-- Claim 2219. -/
def shiftedLogCounterfeitHasNonrealZero : Prop :=
  let radius : ℝ := 1 / (10 : ℝ)^20
  (∃! z : ℂ,
    ‖z - shiftedLogCounterfeitCenter‖ < radius ∧
      shiftedLogCounterfeitSymbol z = 0) ∧
  (∀ z : ℂ,
    ‖z - shiftedLogCounterfeitCenter‖ < radius → z.im ≠ 0)

end
end MathlibPlus.Open.ResearchFormalization
