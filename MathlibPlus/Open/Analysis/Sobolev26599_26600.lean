import Mathlib

open MeasureTheory
open Classical

namespace MathlibPlus.Open.Analysis.R0671

noncomputable section

/-- The finite interval length used by the prefix bounds. -/
def intervalRealLength (a b : ℝ) : ℝ :=
  |b - a|

/-- The powered prefix mass. -/
def prefixMass {M p : ℕ} (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ) : ℝ :=
  ∑ n : Fin (M + 1),
    ∫ u in Set.uIcc a b, ‖R n u‖ ^ (2 * p)

/-- The complex-carrier angular term. -/
def prefixAngularEnergy {M p : ℕ} (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ) : ℝ :=
  (p : ℝ) * ∑ n : Fin (M + 1),
    ∫ u in Set.uIcc a b,
      ‖R n u‖ ^ (2 * p - 2) *
        Complex.im (deriv (R n) u * (starRingEnd ℂ) (R n u))

/-- The complex-carrier derivative energy. -/
def prefixDerivativeEnergy {M p : ℕ} (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ) : ℝ :=
  (p : ℝ) ^ 2 * ∑ n : Fin (M + 1),
    ∫ u in Set.uIcc a b,
      ‖R n u‖ ^ (2 * p - 2) * ‖deriv (R n) u‖ ^ 2

/-- The powered complex Sobolev right-hand side. -/
def complexPrefixBound {p : ℕ}
    (A L C D : ℝ) : ℝ :=
  (A / L + 2 * Real.sqrt (A * (D - C ^ 2 / A))) ^
    ((1 : ℝ) / (2 * (p : ℝ)))

/-- The radial weight, with its continuous-at-zero convention made explicit. -/
def radialWeight (p : ℕ) (r : ℝ) : ℝ :=
  if r = 0 then 0 else
    Real.rpow r (((2 * (p : ℤ) - 4 : ℤ) : ℝ))

/-- The radial derivative energy with the zero convention. -/
def radialDerivativeEnergy {M p : ℕ} (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ) : ℝ :=
  (p : ℝ) ^ 2 * ∑ n : Fin (M + 1),
    ∫ u in Set.uIcc a b,
      radialWeight p ‖R n u‖ *
        (Complex.re (deriv (R n) u * (starRingEnd ℂ) (R n u))) ^ 2

/-- The radial Sobolev right-hand side. -/
def radialPrefixBound {p : ℕ} (A L E : ℝ) : ℝ :=
  (A / L + 2 * Real.sqrt (A * E)) ^
    ((1 : ℝ) / (2 * (p : ℝ)))

/-- The all-prefix complex-carrier Sobolev bound. -/
def claim_26599 : Prop :=
  ∀ (M p : ℕ) (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ),
    1 ≤ p → a ≠ b →
      0 < intervalRealLength a b →
        (∀ n : Fin (M + 1), AbsolutelyContinuousOnInterval (R n) a b) →
          let L := intervalRealLength a b
          let A := prefixMass (p := p) a b R
          let C := prefixAngularEnergy (p := p) a b R
          let D := prefixDerivativeEnergy (p := p) a b R
          A > 0 →
            ∀ u ∈ Set.uIcc a b, ∀ n : Fin (M + 1),
              ‖R n u‖ ≤ complexPrefixBound (p := p) A L C D

/-- The all-prefix radial Sobolev bound. -/
def claim_26600 : Prop :=
  ∀ (M p : ℕ) (a b : ℝ)
    (R : Fin (M + 1) → ℝ → ℂ),
    1 ≤ p → a ≠ b →
      0 < intervalRealLength a b →
        (∀ n : Fin (M + 1), AbsolutelyContinuousOnInterval (R n) a b) →
          let L := intervalRealLength a b
          let A := prefixMass (p := p) a b R
          let E := radialDerivativeEnergy (p := p) a b R
          ∀ u ∈ Set.uIcc a b, ∀ n : Fin (M + 1),
            ‖R n u‖ ≤ radialPrefixBound (p := p) A L E

end

end MathlibPlus.Open.Analysis.R0671
