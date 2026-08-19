import Mathlib

open Polynomial

namespace MathlibPlus.Open.ResearchFormalization.BatchR0758R0771

/-- Claim 24514: the displayed cubic is a majorant for the logarithm on the
full stated interval. -/
def claim24514_rationalCubicMajorantLog : Prop :=
  ∀ y : ℝ, 0 < y → y ≤ 4 →
    (23 / 625 : ℝ) * Real.log y ≤
      6883 / 10000 - (35737 / 10000 : ℝ) * y +
        (6067 / 1250 : ℝ) * y ^ 2 - y ^ 3

/-- The complete elementary state of a multiplicity-three cavity multiset. -/
def cubicState {R : Type*} [CommRing R] (A B C : R) : R × R × R :=
  (A + B + C, A * B + A * C + B * C, A * B * C)

/-- The associated monic split cubic. -/
noncomputable def splitCubic {R : Type*} [CommRing R]
    (A B C : R) : Polynomial R :=
  (X - Polynomial.C A) * (X - Polynomial.C B) *
    (X - Polynomial.C C)

/-- Claim 24588: the three elementary symmetric coordinates and the monic
split cubic encode the same multiplicity-three cavity state. -/
def claim24588_completeCubicCharacteristicState : Prop :=
  ∀ {R : Type*} [CommRing R] (A B C : R),
    cubicState A B C =
        (A + B + C, A * B + A * C + B * C, A * B * C) ∧
      (splitCubic A B C).Monic ∧
      splitCubic A B C =
        X ^ 3 - Polynomial.C (A + B + C) * X ^ 2 +
          Polynomial.C (A * B + A * C + B * C) * X -
            Polynomial.C (A * B * C)

end MathlibPlus.Open.ResearchFormalization.BatchR0758R0771
