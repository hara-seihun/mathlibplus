import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

/-- The endpoint algebra behind the division-free pressure certificate. -/
def divisionFreeTwoEndpointPressureBudget : Prop :=
  ∀ (d B P Ja Jb Jpa Jpb : ℝ),
    0 < Ja * Jb →
    P = d * (Jpb * Ja - Jpa * Jb) / (2 * Ja * Jb) →
      (P ≤ B ↔ d * (Jpb * Ja - Jpa * Jb) ≤ 2 * B * Ja * Jb)

/-- The rootwise phase-current formulas, written in terms of the two endpoint jets. -/
def rootwisePhaseCurrentFormulas : Prop :=
  ∀ (y : ℝ) (e1 e2 : ℂ) (h1 h2 : ℝ),
    y ≠ 0 →
    h1 = 2 * e1.re →
    h2 = 2 * e2.re →
    let e : ℂ := (y : ℂ) * Complex.I
    let J : ℝ := -(e1 * star e).im
    let Jprime : ℝ := -(e2 * star e + e1 * star e1).im
    J = y * h1 / 2 ∧ Jprime = y * h2 / 2

/-- At a simple real zero, the phase-current ratio is the endpoint logarithmic jet. -/
def phaseCurrentRatioEqualsEndpointJet : Prop :=
  ∀ (y : ℝ) (e1 e2 : ℂ) (h1 h2 : ℝ),
    y ≠ 0 →
    h1 ≠ 0 →
    h1 = 2 * e1.re →
    h2 = 2 * e2.re →
    let e : ℂ := (y : ℂ) * Complex.I
    let J : ℝ := -(e1 * star e).im
    let Jprime : ℝ := -(e2 * star e + e1 * star e1).im
    Jprime / J = h2 / h1

/-- The carrier-corrected endpoint determinant after substituting J = rho^2 K. -/
def carrierCorrectedDivisionFreeDeterminant : Prop :=
  ∀ (B d rhoA rhoB KA KB KpA KpB uA uB : ℝ),
    0 < rhoA →
    0 < rhoB →
    0 < KA * KB →
    let JA : ℝ := rhoA ^ 2 * KA
    let JB : ℝ := rhoB ^ 2 * KB
    let JpA : ℝ := rhoA ^ 2 * (KpA + 2 * uA * KA)
    let JpB : ℝ := rhoB ^ 2 * (KpB + 2 * uB * KB)
    let determinantJ : ℝ :=
      2 * B * JA * JB - d * (JpB * JA - JpA * JB)
    let determinantK : ℝ :=
      2 * B * KA * KB -
        d * ((KpB + 2 * uB * KB) * KA -
          (KpA + 2 * uA * KA) * KB)
    let pressure : ℝ :=
      d * (JpB * JA - JpA * JB) / (2 * JA * JB)
    determinantJ = rhoA ^ 2 * rhoB ^ 2 * determinantK ∧
      (0 ≤ determinantJ ↔ 0 ≤ determinantK) ∧
      (pressure ≤ B ↔ 0 ≤ determinantK)

end MathlibPlus.Open.ResearchFormalizationBatch
