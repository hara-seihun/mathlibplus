import Mathlib

noncomputable section
open scoped BigOperators
open Filter MeasureTheory Set
open Classical

namespace MathlibPlus.Open.FormalizationBatch.Analytic

abbrev PrimeFilterCoefficients (d : ℕ → ℕ) :=
  ∀ p : ℕ, Fin (d p + 1) → ℂ

def nonzeroPrimeFilterCoefficients
    (P : Finset ℕ) (d : ℕ → ℕ)
    (c : PrimeFilterCoefficients d) : Prop :=
  ∃ p : ℕ, p ∈ P ∧ ∃ j : Fin (d p + 1), c p j ≠ 0

def primeTower (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ,
    Complex.ofReal
        (Real.log (p : ℝ) *
          Real.rpow (p : ℝ) (-((k + 1 : ℕ) : ℝ) / 2)) *
      Complex.exp
        (-Complex.I * Complex.ofReal ((k + 1 : ℕ) : ℝ) *
          Complex.ofReal t * Complex.ofReal (Real.log (p : ℝ)))

def finitePhaseFilter
    (d : ℕ → ℕ) (c : PrimeFilterCoefficients d) (p : ℕ) (t : ℝ) : ℂ :=
  ∑ j : Fin (d p + 1),
    c p j *
      Complex.exp
        (-Complex.I * Complex.ofReal (j.val : ℝ) * Complex.ofReal t *
          Complex.ofReal (Real.log (p : ℝ)))

def filteredPrimeSum
    (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d) (t : ℝ) : ℂ :=
  ∑ p ∈ P, finitePhaseFilter d c p t * primeTower p t

def filterMass
    (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d) : ℝ :=
  ∑ p ∈ P,
    Real.log (p : ℝ) / (Real.sqrt (p : ℝ) - 1) *
      ∑ j : Fin (d p + 1), ‖c p j‖

def quadraticPrimeForm
    (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d) : ℂ :=
  ∑ p ∈ P,
    Complex.ofReal (Real.log (p : ℝ)) ^ 2 /
        Complex.ofReal ((p : ℝ) - 1) *
      ∑ j : Fin (d p + 1), ∑ l : Fin (d p + 1),
        c p j * star (c p l) *
          Complex.ofReal
            (Real.rpow (p : ℝ) (-((Int.natAbs (j.val - l.val) : ℕ) : ℝ) / 2))

def meanSquareAverage
    (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d) (T : ℝ) : ℝ :=
  (1 / T) *
    (∫ t in Set.Icc (0 : ℝ) T, Complex.normSq (filteredPrimeSum P d c t))

def thresholdDensity
    (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d)
    (alpha R T : ℝ) : ℝ :=
  (MeasureTheory.volume
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) T ∧
        ‖filteredPrimeSum P d c t‖ ≥ alpha * R}).toReal / T

def finiteCausalPrimeTowerFilterObstruction : Prop :=
  ∀ (P : Finset ℕ) (d : ℕ → ℕ) (c : PrimeFilterCoefficients d),
    P.Nonempty → (∀ p ∈ P, Nat.Prime p) →
    nonzeroPrimeFilterCoefficients P d c →
    let M := filterMass P d c
    let R2 := quadraticPrimeForm P d c
    let R := Real.sqrt R2.re
    (R2.im = 0 ∧ 0 < R2.re) ∧
    Tendsto (meanSquareAverage P d c) atTop (nhds R2.re) ∧
    (∀ alpha : ℝ, 0 ≤ alpha → alpha < 1 →
      Filter.liminf
          (fun T : ℝ => thresholdDensity P d c alpha R T) atTop ≥
        ((1 - alpha ^ 2) * R2.re) /
          (M ^ 2 - alpha ^ 2 * R2.re) ∧
      0 < ((1 - alpha ^ 2) * R2.re) /
          (M ^ 2 - alpha ^ 2 * R2.re)) ∧
    ¬ Tendsto (meanSquareAverage P d c) atTop (nhds 0)

def unweightedNonlinearLevelLock : Prop :=
  (∀ (lambda1 lambda2 : ℝ) (theta1 theta2 : ℝ),
    0 < lambda1 → 0 < lambda2 →
    lambda2 * theta2 = -lambda1 * theta1 →
    ∀ k : ℝ,
      Real.sinh (k * lambda1 * theta1) +
          Real.sinh (k * lambda2 * theta2) = 0) ∧
  (0 < (1 : ℝ) ∧ 0 < (2 : ℝ) ∧
    (1 : ℝ) ≠ 2 ∧ (1 : ℝ) ≠ 0 ∧ (-(1 / 2 : ℝ)) ≠ 0 ∧
    (2 : ℝ) * (-(1 / 2 : ℝ)) = -(1 : ℝ) * 1 ∧
    (∀ k : ℝ,
      Real.sinh (k * 1 * 1) + Real.sinh (k * 2 * (-(1 / 2 : ℝ))) = 0) ∧
    0 < Real.exp ((1 : ℝ) * 1) ∧
    0 < Real.exp ((2 : ℝ) * (-(1 / 2 : ℝ))))

end MathlibPlus.Open.FormalizationBatch.Analytic
