import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The integer-hold multiplier from the admitted source claims. -/
def qₘ (m : ℕ) (z : ℂ) : ℂ := 1 + z ^ (4 * m)

/-- The listed roots of the integer-hold multiplier. -/
noncomputable def qRootₘ (m j : ℕ) : ℂ :=
  Complex.exp
    (((((2 * j + 1 : ℕ) : ℂ) * (Real.pi : ℂ)) * Complex.I) /
      ((4 * m : ℕ) : ℂ))

/-- A point on the centered critical axis. -/
def criticalAxisPoint (t : ℝ) : ℂ := (t : ℂ) * Complex.I

/-- Claim 11235: the complete off-axis zero set of `Q_m`, including its quartet
symmetries. -/
def claim11235_exactZeroSet : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ z : ℂ,
      qₘ m z = 0 ↔ ∃ j : ℕ, j < 4 * m ∧ z = qRootₘ m j) ∧
    (∀ j : ℕ, j < 4 * m →
      (qRootₘ m j).re ≠ 0 ∧ (qRootₘ m j).im ≠ 0) ∧
    (∀ j k : ℕ, j < 4 * m → k < 4 * m → j ≠ k →
      qRootₘ m j ≠ qRootₘ m k) ∧
    (∀ z : ℂ, qₘ m z = 0 →
      qₘ m (-z) = 0 ∧
      qₘ m (starRingEnd ℂ z) = 0 ∧
      qₘ m (-(starRingEnd ℂ z)) = 0 ∧
      z ≠ -z ∧
      z ≠ starRingEnd ℂ z ∧
      z ≠ -(starRingEnd ℂ z))

/-- Claim 11240: positivity on the critical axis, sign preservation for every
real-valued critical-axis carrier, and planting of every multiplier zero. -/
def claim11240_axisSignAndPlanting : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ t : ℝ,
      qₘ m (criticalAxisPoint t) = (1 + t ^ (4 * m) : ℂ) ∧
      0 < 1 + t ^ (4 * m)) ∧
    (∀ F : ℂ → ℂ,
      (∀ t : ℝ, (F (criticalAxisPoint t)).im = 0) →
      ∀ t : ℝ,
        (F (criticalAxisPoint t) * qₘ m (criticalAxisPoint t)).im = 0 ∧
        ((F (criticalAxisPoint t)).re = 0 ↔
          (F (criticalAxisPoint t) * qₘ m (criticalAxisPoint t)).re = 0) ∧
        ((F (criticalAxisPoint t)).re > 0 ↔
          (F (criticalAxisPoint t) * qₘ m (criticalAxisPoint t)).re > 0) ∧
        ((F (criticalAxisPoint t)).re < 0 ↔
          (F (criticalAxisPoint t) * qₘ m (criticalAxisPoint t)).re < 0)) ∧
    (∀ (F : ℂ → ℂ) (z : ℂ), qₘ m z = 0 →
      F z * qₘ m z = 0)

/-- The maximum modulus on a closed disk. -/
noncomputable def maximumModulus (F : ℂ → ℂ) (r : ℝ) : ENNReal :=
  ⨆ z : {z : ℂ // ‖z‖ ≤ r}, ENNReal.ofReal ‖F z.1‖

/-- The standard entire-function growth order, using the limsup of
`log (log M(r)) / log r` at infinity. -/
noncomputable def entireOrder (F : ℂ → ℂ) : ENNReal :=
  Filter.limsup
    (fun r : ℝ =>
      ENNReal.ofReal
          (max 0 (Real.log (max 1 (Real.log (max 1 (maximumModulus F r).toReal))))) /
        ENNReal.ofReal (max 0 (Real.log (max 1 r))))
    Filter.atTop

/-- Positive finite order for an entire carrier. -/
def hasPositiveFiniteOrder (F : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ F Set.univ ∧
  0 < entireOrder F ∧ entireOrder F < ⊤

/-- The concrete eligibility data used by the finite-jet obstruction. -/
def eligibleCarrier (F : ℂ → ℂ) : Prop :=
  hasPositiveFiniteOrder F ∧
  (∀ z : ℂ, F (-z) = F z) ∧
  (∀ z : ℂ, F (starRingEnd ℂ z) = starRingEnd ℂ (F z)) ∧
  (∀ t : ℝ, (F (criticalAxisPoint t)).im = 0)

/-- The data visible through a finite central jet and the stated symmetries,
order, and critical-axis sign. -/
def sameFiniteJetSymmetryOrderSignData (N : ℕ) (F G : ℂ → ℂ) : Prop :=
  eligibleCarrier F ∧
  eligibleCarrier G ∧
  entireOrder F = entireOrder G ∧
  (∀ k : ℕ, k ≤ N → iteratedDeriv k F 0 = iteratedDeriv k G 0) ∧
  (∀ t : ℝ,
    ((F (criticalAxisPoint t)).re = 0 ↔
      (G (criticalAxisPoint t)).re = 0) ∧
    ((F (criticalAxisPoint t)).re > 0 ↔
      (G (criticalAxisPoint t)).re > 0) ∧
    ((F (criticalAxisPoint t)).re < 0 ↔
      (G (criticalAxisPoint t)).re < 0))

/-- Coordinate-axis support of the zero set. -/
def zerosOnCoordinateAxes (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F z = 0 → z.re = 0 ∨ z.im = 0

/-- Claim 11241: arbitrary finite central data together with the stated
symmetries, positive finite order, and critical-axis sign cannot force
coordinate-axis localization. -/
def claim11241_noFiniteJetAxisLocalization : Prop :=
  ∀ N : ℕ, ∃ m : ℕ, 4 * m > N ∧
    ∀ F : ℂ → ℂ, eligibleCarrier F →
      let G : ℂ → ℂ := fun z => F z * qₘ m z
      sameFiniteJetSymmetryOrderSignData N F G ∧
      (∀ k : ℕ, k < 4 * m →
        iteratedDeriv k F 0 = iteratedDeriv k G 0) ∧
      (∀ j : ℕ, j < 4 * m →
        (qRootₘ m j).re ≠ 0 ∧
        (qRootₘ m j).im ≠ 0 ∧
        G (qRootₘ m j) = 0) ∧
      ¬ zerosOnCoordinateAxes G ∧
      ¬ (∀ H : ℂ → ℂ,
        sameFiniteJetSymmetryOrderSignData N F H →
          zerosOnCoordinateAxes H)

end MathlibPlus.Open.Analysis
