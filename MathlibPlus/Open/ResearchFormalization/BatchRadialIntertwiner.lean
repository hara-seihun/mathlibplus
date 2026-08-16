import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner

abbrev L2Unit := MeasureTheory.Lp ℝ 2 (volume.restrict (Set.Ioo (0 : ℝ) 1))

def radialU (f : L2Unit) (x : ℝ) : ℝ :=
  if |x| < 1 then Real.sqrt (1 / 2) * f |x| else 0

def radialPhi (t : ℝ) (f : L2Unit) (u : ℝ) : ℝ :=
  Real.sqrt (t / 2) * radialU f (t * u / 2)

def archimedeanConstant (t : ℝ) : ℝ :=
  (1 / 2) * Real.log (t / (4 * Real.pi)) - Real.eulerMascheroniConstant / 2

def archimedeanKernel (u : ℝ) : ℝ :=
  if u = 0 then 1 / 4 else
    -u * Real.exp u + u * Real.exp (-5 * u) / (1 - Real.exp (-4 * u))

def radialAplus (t : ℝ) (f : L2Unit) : ℝ :=
  archimedeanConstant t * ‖f‖ ^ 2
    + (1 / 8) *
        (∫ x, (∫ y,
          ((f x - f y) ^ 2 / |x - y|) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)))
          ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)))
    - (1 / 4) *
        (∫ x in Set.Ioo (0 : ℝ) 1,
          Real.log (x * (1 - x)) * f x ^ 2)
    - (∫ x in Set.Ioo (0 : ℝ) 1,
        (∫ y in Set.Ioo (0 : ℝ) 1,
          ((archimedeanKernel (|x - y| / t) - 1 / 4) / |x - y|) * f x * f y))
    - (∫ x in Set.Ioo (0 : ℝ) 1,
        (∫ y in Set.Ioo (0 : ℝ) 1,
          (archimedeanKernel ((x + y) / t) / (x + y)) * f x * f y))

def compressedShiftPairing (a : ℝ) (f : L2Unit) : ℝ :=
  (∫ x : ℝ, radialU f (x + a) * radialU f x)
    + (∫ x : ℝ, radialU f (x - a) * radialU f x)

def radialAfull (t : ℝ) (f : L2Unit) : ℝ :=
  radialAplus t f - (1 / 2) *
    ∑' n : {n : ℕ // 2 ≤ n},
      (ArithmeticFunction.vonMangoldt n.1 / Real.sqrt (n.1 : ℝ)) *
        compressedShiftPairing (t * Real.log (n.1 : ℝ) / 2) f

def testFourierTransform (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))

def testH (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  testFourierTransform φ z * star (testFourierTransform φ (star z))

def testAutocorrelation (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u : ℝ, φ (u + x) * φ u

def weilQuadraticForm (φ : ℝ → ℝ) : ℝ :=
  Complex.re
    (testH φ (Complex.I / 2) + testH φ ((-Complex.I) / 2)
      - (Real.log Real.pi : ℂ) * (testAutocorrelation φ 0 : ℂ)
      + (1 / (2 * (Real.pi : ℂ))) *
          (∫ s : ℝ,
            testH φ (s : ℂ) *
              ((Complex.digamma
                (1 / 4 + Complex.I * (s : ℂ) / 2)).re : ℂ))
      - (2 : ℂ) *
          ∑' n : {n : ℕ // 2 ≤ n},
            ((ArithmeticFunction.vonMangoldt n.1 : ℂ) /
                (Real.sqrt (n.1 : ℝ) : ℂ)) *
              (testAutocorrelation φ (Real.log (n.1 : ℝ)) : ℂ))

def realEvenCompactTest (φ : ℝ → ℝ) : Prop :=
  Function.Even φ ∧ IsCompact (tsupport φ)

def supportedIn (radius : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ u : ℝ, radius ≤ |u| → φ u = 0

def claim10350 : Prop :=
  ∀ (t : ℝ), 0 < t →
    ∀ (f : L2Unit),
      radialAfull t f = (1 / 2) * weilQuadraticForm (radialPhi t f)

def claim10353 : Prop :=
  ∀ (t : ℝ), 0 < t →
    ((∀ f : L2Unit, 0 ≤ radialAfull t f) ↔
      ∀ φ : ℝ → ℝ,
        realEvenCompactTest φ ∧ supportedIn (2 / t) φ →
          0 ≤ weilQuadraticForm φ)

def claim10354 : Prop :=
  ((∀ (t : ℝ), 0 < t → ∀ f : L2Unit, 0 ≤ radialAfull t f) ↔
    RiemannHypothesis)

end MathlibPlus.Open.ResearchFormalization.BatchRadialIntertwiner
