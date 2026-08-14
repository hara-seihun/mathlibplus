import Mathlib

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.Geometry

/- Claim 53137. -/
def finiteCoreGap (i : ℤ) : ℝ :=
  if |i| ≤ 160 then
    (32 : ℝ) / 33 * ((1 : ℝ) / 32 + (2 : ℝ) ^ (-|i| : ℤ))
  else 1

def finiteCorePosition (i : ℤ) : ℝ :=
  if 0 ≤ i then
    Finset.sum (Finset.Ico (0 : ℤ) i) finiteCoreGap
  else
    -(Finset.sum (Finset.Ico i (0 : ℤ)) finiteCoreGap)

def finiteCoreGapTrainClaim : Prop :=
  (∀ i : ℤ, 0 < finiteCoreGap i) ∧
    (∀ i : ℤ, finiteCoreGap (-i) = finiteCoreGap i) ∧
    finiteCoreGap 0 = 1 ∧
    finiteCoreGap 1 = (17 : ℝ) / 33 ∧
    finiteCoreGap (-1) = (17 : ℝ) / 33 ∧
    finiteCorePosition 0 = 0 ∧
    (∀ i : ℤ,
      finiteCorePosition (i + 1) = finiteCorePosition i + finiteCoreGap i) ∧
    (∀ i j : ℤ, i < j → finiteCorePosition i < finiteCorePosition j) ∧
    (∀ i : ℤ, 162 ≤ i →
      finiteCorePosition i = (i : ℝ) +
        (finiteCorePosition 162 - (162 : ℝ))) ∧
    (∀ i : ℤ, i ≤ -161 →
      finiteCorePosition i = (i : ℝ) +
        (finiteCorePosition (-161) - (-161 : ℝ)))

/- Claim 54095. -/
def exactFiniteEdgeTargetGeometry : Prop :=
  let L : ℝ := (1529 : ℝ) / 10000
  let t : ℝ := (44658961 : ℝ) / 312500000
  let y : ℝ := (1767 : ℝ) / 12500
  let X : ℝ := 6000000185827
  let N : ℝ := 2430000
  let I : Set ℝ := Set.Icc
    (X + Real.sqrt (1 - y ^ 2))
    (4 * Real.pi * (N ^ 2 - t / 16))
  let m₀ : ℝ := 1555542143090
  let x₀ : ℝ := (4 * Real.pi * m₀ - Real.pi / 2) / Real.log 2
  x₀ ∈ I

/- Claim 54097. -/
def literalPrimeCarrier (x : ℝ) (r : ℕ) : ℂ :=
  Complex.exp
    (-Complex.I * (x : ℂ) * (Real.log (r : ℝ) : ℂ) / (2 : ℂ))

def edgeHitX₀ : ℝ :=
  (4 * Real.pi * (1555542143090 : ℝ) - Real.pi / 2) / Real.log 2

def literalPrimeCarrierPhaseClaim : Prop :=
  literalPrimeCarrier edgeHitX₀ 2 = Complex.exp (Complex.I * Real.pi / 4) ∧
    ‖literalPrimeCarrier edgeHitX₀ 3 -
        Complex.exp (Complex.I * ((7864242794387306 : ℝ) / 10000000000000000))‖
      < (1 : ℝ) / 1000000000000000

end MathlibPlus.Open.FormalizationBatch.Geometry
