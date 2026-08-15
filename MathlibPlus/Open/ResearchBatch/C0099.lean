import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.C0099

def vkScale (L : ℝ) : ℝ :=
  Real.rpow L (3 / 5 : ℝ) / Real.rpow (Real.log L) (1 / 5 : ℝ)

def finitePsiEnvelope (A p d x : ℝ) : ℝ :=
  A * x * Real.rpow (Real.log x) p * Real.exp (-d * vkScale (Real.log x))

def vkScaleAndEnvelope_claim1507 :
    (ℝ → ℝ) × (ℝ → ℝ → ℝ → ℝ → ℝ) :=
  (vkScale, finitePsiEnvelope)

def vkTransferQ (c : ℝ) : ℝ :=
  Real.rpow (5 / (3 * c^3) : ℝ) (1 / 5 : ℝ) *
    (Real.rpow (3 / 2 : ℝ) (2 / 5 : ℝ) +
      Real.rpow (2 / 3 : ℝ) (3 / 5 : ℝ))

def repairedDensityTail_claim1516 (L : ℝ) : ℝ × ℝ × ℝ :=
  let sigma : ℝ := 0.9999714
  let B₃ : ℝ := 0.21617
  let C₁ : ℝ := 17.418
  let C₂ : ℝ := 2.077
  let H : ℝ := 3000175332800
  let Q : ℝ := vkTransferQ 51.3401
  let r : ℝ := vkScale L
  let p : ℝ := 5 - 2 * sigma
  let a : ℝ := (5 - 8 * sigma) / 3
  let s₁ : ℝ :=
    Real.exp (-L / 2) * Real.log (H / (2 * Real.pi))^2 / (2 * Real.pi) +
      Real.exp (-(1 - sigma) * L) *
        (B₃^2 * r^2 / (2 * Real.pi) -
          Real.log (H / (2 * Real.pi))^2 / (2 * Real.pi) + 1.8642)
  let s₂ : ℝ :=
    2 * C₁ * Real.exp (a * Q * r) * Real.rpow (Q * r) p +
      2 * C₂ * Real.exp (-Q * r) * Real.rpow (Q * r) 2
  let s₃ : ℝ := 4.3128 * Real.rpow L 0.6 * Real.exp (-Q * r)
  (s₁, s₂, s₃)

end MathlibPlus.Open.ResearchBatch.C0099
