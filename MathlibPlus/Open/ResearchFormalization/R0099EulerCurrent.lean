import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent

open scoped BigOperators

noncomputable section

abbrev BivariateSeries (R : Type*) [CommRing R] := PowerSeries (PowerSeries R)

def eulerOperator {R : Type*} [CommRing R] (H : PowerSeries R) : PowerSeries R :=
  PowerSeries.X * PowerSeries.derivative R H

def firstVariableSeries {R : Type*} [CommRing R] (H : PowerSeries R) : BivariateSeries R :=
  PowerSeries.map (PowerSeries.C : R →+* PowerSeries R) H

def secondVariableSeries {R : Type*} [CommRing R] (H : PowerSeries R) : BivariateSeries R :=
  PowerSeries.C H

def eulerCurrent {R : Type*} [CommRing R] (H : PowerSeries R) : BivariateSeries R :=
  firstVariableSeries H * secondVariableSeries (eulerOperator H) -
    firstVariableSeries (eulerOperator H) * secondVariableSeries H

def swapBivariate {R : Type*} [CommRing R] (S : BivariateSeries R) : BivariateSeries R :=
  PowerSeries.mk (fun i =>
    PowerSeries.mk (fun j =>
      PowerSeries.coeff i (PowerSeries.coeff j S)))

def diagonalBivariate {R : Type*} [CommRing R] (S : BivariateSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n =>
    ∑ i ∈ Finset.range (n + 1),
      PowerSeries.coeff (n - i) (PowerSeries.coeff i S))

def truncatePowerSeries {R : Type*} [CommRing R] (N : ℕ) (H : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (fun n => if n < N then PowerSeries.coeff n H else 0)

def eulerDivisor {R : Type*} [CommRing R] : BivariateSeries R :=
  PowerSeries.C (PowerSeries.X : PowerSeries R) - PowerSeries.X

/-- Claim 17931: the universal Euler current is antisymmetric, has zero
formal diagonal, and every finite truncation is divisible by `w - z`. -/
def eulerCurrentAntisymmetry_claim17931 : Prop :=
  ∀ (R : Type*) [CommRing R] (H : PowerSeries R),
    swapBivariate (eulerCurrent H) = -eulerCurrent H ∧
      diagonalBivariate (eulerCurrent H) = 0 ∧
        ∀ N : ℕ, eulerDivisor ∣ eulerCurrent (truncatePowerSeries N H)

def antiDiagonalLength (i j : ℕ) : ℕ := i + j + 1

def cutIncidence (a i j : ℕ) : Prop := a ≤ i ∧ a ≤ j

def eulerQuotientCoefficient {R : Type*} [CommRing R]
    (H : PowerSeries R) (i j : ℕ) : R :=
  ∑ a ∈ Finset.range (min i j + 1),
    ((antiDiagonalLength i j - 2 * a : ℕ) : R) *
      PowerSeries.coeff a H *
        PowerSeries.coeff (antiDiagonalLength i j - a) H

def eulerQuotient {R : Type*} [CommRing R]
    (H : PowerSeries R) : BivariateSeries R :=
  PowerSeries.mk (fun i =>
    PowerSeries.mk (fun j => eulerQuotientCoefficient H i j))

/-- Claim 17935: the anti-diagonal, reflection, and cut-incidence data are
consequences of dividing the explicitly defined Euler current by `w - z`. -/
def eulerCurrentIntervalDerivation_claim17935 : Prop :=
  ∀ (R : Type*) [CommRing R] (H : PowerSeries R),
    swapBivariate (eulerCurrent H) = -eulerCurrent H ∧
      diagonalBivariate (eulerCurrent H) = 0 ∧
        eulerDivisor * eulerQuotient H = eulerCurrent H ∧
          (∀ i j : ℕ,
            PowerSeries.coeff j (PowerSeries.coeff i (eulerQuotient H)) =
              ∑ a ∈ Finset.range (min i j + 1),
                ((antiDiagonalLength i j - 2 * a : ℕ) : R) *
                  PowerSeries.coeff a H *
                    PowerSeries.coeff (antiDiagonalLength i j - a) H) ∧
            (∀ i j : ℕ,
              eulerQuotientCoefficient H i j =
                eulerQuotientCoefficient H j i) ∧
              (∀ a i j : ℕ,
                (a ∈ Finset.range (min i j + 1) ↔ cutIncidence a i j))

end

end MathlibPlus.Open.ResearchFormalization.R0099EulerCurrent
