import Mathlib

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.O0319

abbrev ShiftMeasure := MeasureTheory.Measure NNReal

def positiveFiniteMeasure (μ : ShiftMeasure) : Prop :=
  IsFiniteMeasure μ ∧ 0 < Measure.real μ Set.univ

def shiftLaplaceKernel (μ : ShiftMeasure) (u : ℝ) : ℝ :=
  ∫ r, Real.exp (-((r : ℝ) * u)) ∂μ

def shiftResolvent (μ : ShiftMeasure) (z : ℂ) : ℂ :=
  ∫ r, 1 / (z + ((r : ℝ) : ℂ)) ∂μ

/-- Claim 14165. -/
def claim14165 : Prop :=
  ∀ μ : ShiftMeasure, positiveFiniteMeasure μ →
    shiftLaplaceKernel μ 0 = Measure.real μ Set.univ ∧
      (∀ z : ℂ, 0 < z.re → 0 < (shiftResolvent μ z).re) ∧
      (∀ δ : ℝ, 0 < δ →
        (shiftResolvent μ (δ : ℂ)).re ≤ Measure.real μ Set.univ / δ)

def shiftedLogDerivative (μ : ShiftMeasure) (s : ℂ) : ℂ :=
  ∫ r,
    -(deriv riemannZeta (s + ((r : ℝ) : ℂ))) /
      riemannZeta (s + ((r : ℝ) : ℂ)) ∂μ

def primeFieldTerm (μ : ShiftMeasure) (s : ℂ) (n : ℕ) : ℂ :=
  if 2 ≤ n then
    (ArithmeticFunction.vonMangoldt n : ℝ) *
        Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) *
      (shiftLaplaceKernel μ (Real.log (n : ℝ)) : ℂ)
  else 0

/-- Claim 14166. -/
def claim14166 : Prop :=
  ∀ μ : ShiftMeasure, positiveFiniteMeasure μ → ∀ s : ℂ, 1 < s.re →
    shiftedLogDerivative μ s = ∑' n : ℕ, primeFieldTerm μ s n

def trigonometricPacket (a : ℕ → ℝ) (m : ℕ) (v : ℝ) : ℝ :=
  a 0 + ∑ k ∈ Finset.range m,
    a (k + 1) * Real.cos ((k + 1 : ℕ) * v)

def primePacketLeft (μ : ShiftMeasure) (a : ℕ → ℝ) (m : ℕ)
    (σ T : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    a k * (shiftedLogDerivative μ
      ((σ : ℂ) + Complex.I * (((k : ℝ) * T : ℝ) : ℂ))).re

def primePacketRight (μ : ShiftMeasure) (a : ℕ → ℝ) (m : ℕ)
    (σ T : ℝ) : ℝ :=
  ∑' n : ℕ,
    if 2 ≤ n then
      (ArithmeticFunction.vonMangoldt n : ℝ) *
          Real.rpow (n : ℝ) (-σ) *
        shiftLaplaceKernel μ (Real.log (n : ℝ)) *
          trigonometricPacket a m (T * Real.log (n : ℝ))
    else 0

/-- Claim 14167. -/
def claim14167 : Prop :=
  ∀ (μ : ShiftMeasure) (a : ℕ → ℝ) (m : ℕ) (σ T : ℝ),
    positiveFiniteMeasure μ → 1 ≤ m → 1 < σ →
    (∀ v : ℝ, 0 ≤ trigonometricPacket a m v) ∧
      (∀ k : ℕ, k ≤ m → 0 ≤ a k) ∧ 0 < a 1 →
      0 ≤ primePacketLeft μ a m σ T ∧
        primePacketLeft μ a m σ T = primePacketRight μ a m σ T

def digammaHalfArgument (σ r : ℝ) (k : ℕ) (T : ℝ) : ℂ :=
  ((σ + r : ℝ) : ℂ) / 2 +
    Complex.I * (((k : ℝ) * T : ℝ) : ℂ) / 2

/-- Claim 14170. -/
def claim14170 : Prop :=
  ∀ σ : ℝ, ∃ Cσ T₀ : ℝ, 0 < T₀ ∧
    ∀ r : ℝ, 0 ≤ r → ∀ k : ℕ, 1 ≤ k → ∀ T : ℝ, T₀ ≤ T →
      (Complex.digamma (digammaHalfArgument σ r k T)).re ≥
        Real.log T - Cσ

def higherDerivativeKernel (q : ℕ) (z : ℂ) : ℂ :=
  (q.factorial : ℂ) / z ^ (q + 1)

def primePowerWeight (q : ℕ) (u : ℝ) : ℝ := u ^ q

/-- Claim 14174. -/
def claim14174 : Prop :=
  ∀ q : ℕ, 1 ≤ q →
    primePowerWeight q 0 = 0 ∧
      (∃ zPos zNeg : ℂ, 0 < zPos.re ∧ 0 < zNeg.re ∧
        0 < (higherDerivativeKernel q zPos).re ∧
        (higherDerivativeKernel q zNeg).re < 0)

end MathlibPlus.Open.ResearchFormalization.O0319
