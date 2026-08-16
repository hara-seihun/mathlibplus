import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus
namespace Open
namespace ResearchFormalization

noncomputable section

def unitInterval : Set ℝ := Set.Ioo 0 1

def unitIntervalL2 (f : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable f (volume.restrict unitInterval) ∧
    Integrable (fun x => f x ^ 2) (volume.restrict unitInterval)

def eulerGamma : ℝ := Real.eulerMascheroniConstant

def dInfinity (u : ℝ) : ℝ :=
  if u = 0 then (1 : ℝ) / 4
  else -u * Real.exp u + u * Real.exp (-5 * u) / (1 - Real.exp (-4 * u))

def vonMangoldtReal (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

def radialU (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if |x| < 1 then (1 / Real.sqrt 2) * f |x| else 0

def translate (a : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  h (x - a)

def compressedShiftQuadratic (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, radialU f x *
    (translate a (radialU f) x + translate (-a) (radialU f) x)

def radialScalar (t : ℝ) : ℝ :=
  (1 / 2) * Real.log (t / (4 * Real.pi)) - eulerGamma / 2

def radialPlus (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  radialScalar t * (∫ x in unitInterval, f x ^ 2) +
    (1 / 8) * (∫ x in unitInterval, ∫ y in unitInterval,
      (f x - f y) ^ 2 / |x - y|) -
    (1 / 4) * (∫ x in unitInterval,
      Real.log (x * (1 - x)) * f x ^ 2) -
    (∫ x in unitInterval, ∫ y in unitInterval,
      (dInfinity (|x - y| / t) - 1 / 4) / |x - y| * f x * f y) -
    (∫ x in unitInterval, ∫ y in unitInterval,
      dInfinity ((x + y) / t) / (x + y) * f x * f y)

def radialFull (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  radialPlus t f -
    (1 / 2) * ∑' n : {n : ℕ // 2 ≤ n},
      (vonMangoldtReal n.1 / Real.sqrt (n.1 : ℝ)) *
        compressedShiftQuadratic (t * Real.log (n.1 : ℝ) / 2) f

def supportRestriction (q Q : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (Q / q) * f (Q * x / q) *
    if x ∈ Set.Ioo 0 (q / Q) then 1 else 0

def claim10357 : Prop :=
  ∀ (q Q : ℝ), 0 < q → q ≤ Q →
    ∀ f : ℝ → ℝ, unitIntervalL2 f →
      radialFull (4 / q) f =
        radialFull (4 / Q) (supportRestriction q Q f)

def testFourier (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, (φ u : ℂ) * Complex.exp (Complex.I * z * (u : ℂ))

def testH (φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  testFourier φ z * starRingEnd ℂ (testFourier φ (starRingEnd ℂ z))

def testAutocorrelation (φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v : ℝ, φ v * φ (v + u)

def weilForm (φ : ℝ → ℝ) : ℝ :=
  (testH φ (Complex.I / 2)).re + (testH φ (-Complex.I / 2)).re -
    Real.log Real.pi * testAutocorrelation φ 0 +
    (1 / (2 * Real.pi)) *
      (∫ s : ℝ,
        (testH φ (s : ℂ)).re *
          (Complex.digamma (1 / 4 + Complex.I * (s : ℂ) / 2)).re) -
    2 * ∑' n : {n : ℕ // 2 ≤ n},
      (vonMangoldtReal n.1 / Real.sqrt (n.1 : ℝ)) *
        testAutocorrelation φ (Real.log (n.1 : ℝ))

def dilatedTest (t : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt (t / 2) * radialU f (t * u / 2)

def discrepancyQ (u : ℝ) : ℝ :=
  (∑' n : {n : ℕ // Real.log (n : ℝ) ≤ u},
      vonMangoldtReal n.1 / Real.sqrt (n.1 : ℝ)) -
    2 * (Real.exp (u / 2) - 1)

def discrepancyAInfinity (u : ℝ) : ℝ :=
  ∫ v in Set.Ioi u, Real.exp (-5 * v / 2) / (1 - Real.exp (-2 * v))

def discrepancyKappa : ℝ :=
  (1 / 2) * (Real.log (8 * Real.pi) + eulerGamma + Real.pi / 2 - 4)

def completedDiscrepancy (u : ℝ) : ℝ :=
  discrepancyQ u + discrepancyKappa - discrepancyAInfinity u

def discrepancyRepresentation (t : ℝ) (f : ℝ → ℝ) : Prop :=
  radialFull t f =
    ∫ u in Set.Ioc 0 (4 / t),
      completedDiscrepancy u * deriv (fun v => testAutocorrelation
        (dilatedTest t f) v) u

def dilatedTestHasGrowingSupport (t : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ u : ℝ, dilatedTest t f (-u) = dilatedTest t f u) ∧
  (∀ u : ℝ, 2 / t ≤ |u| → dilatedTest t f u = 0)

def claim10360 : Prop :=
  (∀ (t u a : ℝ), 0 < t → 0 < u → a = t * u / 2 →
    (-2 * dInfinity (a / t) / u =
      Real.exp (u / 2) -
        Real.exp (-5 * u / 2) / (1 - Real.exp (-2 * u))) ∧
    (dInfinity (a / t) + (u / 2) * Real.exp (u / 2) =
      (u / 2) * Real.exp (-5 * u / 2) /
        (1 - Real.exp (-2 * u)))) ∧
  Filter.Tendsto (fun s : ℝ => 2 / s)
    (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop ∧
  (∀ f : ℝ → ℝ, unitIntervalL2 f →
    (∀ t : ℝ, 0 < t → discrepancyRepresentation t f) ∧
    (∀ t : ℝ, 0 < t →
      radialFull t f = (1 / 2) * weilForm (dilatedTest t f)) ∧
    (∀ t : ℝ, 0 < t → dilatedTestHasGrowingSupport t f))

end
end ResearchFormalization
end Open
end MathlibPlus
