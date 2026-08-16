import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The full Möbius exponential transform from the admitted dyadic claims. -/
def fullMobiusTransform (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 1 ≤ n then
      (ArithmeticFunction.moebius n : ℝ) * Real.exp (-((n : ℝ) * x))
    else 0

/-- The odd Möbius exponential transform from the admitted dyadic claims. -/
def oddMobiusTransform (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    if n % 2 = 1 then
      (ArithmeticFunction.moebius n : ℝ) * Real.exp (-((n : ℝ) * x))
    else 0

/-- Claim 11163: the odd transform is the complete, rather than finite,
dyadic tower of the full transform. -/
def completeDyadicInversion : Prop :=
  ∀ x : ℝ, 0 < x →
    Summable (fun j : ℕ => fullMobiusTransform (((2 : ℝ) ^ j) * x)) ∧
    oddMobiusTransform x =
      ∑' j : ℕ, fullMobiusTransform (((2 : ℝ) ^ j) * x)

/-- The critical-coordinate fields and their fixed dyadic shift. -/
def criticalFullField (y : ℝ) : ℝ :=
  Real.exp (-y / 2) * fullMobiusTransform (Real.exp (-y))

def criticalOddField (y : ℝ) : ℝ :=
  Real.exp (-y / 2) * oddMobiusTransform (Real.exp (-y))

def criticalDyadicQ : ℝ :=
  Real.rpow 2 (-1 / 2 : ℝ)

def criticalDyadicShift (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f (y - Real.log 2)

def criticalDyadicFilter (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f y - criticalDyadicQ * criticalDyadicShift f y

def criticalDyadicGeometricInverse (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' j : ℕ,
    criticalDyadicQ ^ j * f (y - (j : ℝ) * Real.log 2)

/-- Claim 11164: the exact full and odd transforms obey the critical-coordinate
filter identity and its pointwise complete geometric inverse. -/
def criticalCoordinateFilterIdentity : Prop :=
  (∀ y : ℝ,
    criticalFullField y = criticalDyadicFilter criticalOddField y) ∧
  (∀ y : ℝ,
    Summable (fun j : ℕ =>
      criticalDyadicQ ^ j *
        criticalFullField (y - (j : ℝ) * Real.log 2)) ∧
    criticalOddField y =
      criticalDyadicGeometricInverse criticalFullField y)

/-- One-logarithmic-unit critical energy, using the multiplicative interval
`[a/e,a]`. -/
def oneLogCriticalEnergy (H : ℝ → ℝ) (a : ℝ) : ENNReal :=
  ∫⁻ x in Set.Ioc (a / Real.exp 1) a,
    ENNReal.ofReal ((H x) ^ 2)

def oneLogCriticalSquareRootNorm (H : ℝ → ℝ) : ENNReal :=
  ⨆ a : ℝ,
    if 0 < a then
      ENNReal.rpow (oneLogCriticalEnergy H a) (1 / 2 : ℝ)
    else 0

/-- Claim 11167: finiteness of the scale-uniform one-log critical energy is
unchanged by passing between the exact full and odd fields, with the fixed
square-root factors. -/
def scaleUniformCriticalEnergyEquivalence : Prop :=
  (oneLogCriticalSquareRootNorm fullMobiusTransform ≠ ⊤ ↔
    oneLogCriticalSquareRootNorm oddMobiusTransform ≠ ⊤) ∧
  (ENNReal.ofReal (1 - criticalDyadicQ) *
      oneLogCriticalSquareRootNorm oddMobiusTransform ≤
    oneLogCriticalSquareRootNorm fullMobiusTransform) ∧
  (oneLogCriticalSquareRootNorm fullMobiusTransform ≤
    ENNReal.ofReal (1 + criticalDyadicQ) *
      oneLogCriticalSquareRootNorm oddMobiusTransform)

end MathlibPlus.Open.Analysis
