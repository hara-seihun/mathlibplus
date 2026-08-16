import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch11355

noncomputable section

/-- The coefficient-level finite truncation of q ∏ (1 - q^j)^24. -/
def deltaTrunc (n : ℕ) : Polynomial ℤ :=
  Polynomial.X * Finset.prod (Finset.Icc 1 n)
    (fun j => (1 - Polynomial.X ^ j) ^ 24)

def ramanujanTau (n : ℕ) : ℤ :=
  (deltaTrunc n).coeff n

def heckeA (p : ℕ) : ℂ :=
  (1 : ℂ) + (p : ℂ) ^ 11

def heckeB (p : ℕ) : ℂ :=
  (ramanujanTau p : ℂ)

def unitaryScale (p : ℕ) : ℂ :=
  Complex.ofReal (Real.rpow (p : ℝ) (11 / 2 : ℝ))

def unitaryA (p : ℕ) : ℂ :=
  heckeA p / unitaryScale p

def unitaryB (p : ℕ) : ℂ :=
  heckeB p / unitaryScale p

def quadraticContraction (c₀ c₁ c₂ : ℂ) (p : ℕ) : ℂ :=
  c₀ * unitaryA p ^ 2 + c₁ * unitaryA p * unitaryB p + c₂ * unitaryB p ^ 2

def quadraticContractionNoGo : Prop :=
  ¬ ∃ c₀ c₁ c₂ : ℂ,
    ∀ p : ℕ, Nat.Prime p → quadraticContraction c₀ c₁ c₂ p = 2

def augmentedRow (p : ℕ) : Fin 4 → ℂ :=
  ![heckeA p ^ 2, heckeA p * heckeB p, heckeB p ^ 2,
    (2 : ℂ) * (p : ℂ) ^ 11]

def augmentedMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  ![augmentedRow 2, augmentedRow 3, augmentedRow 5, augmentedRow 7]

def fourPrimeDeterminant : ℂ :=
  Matrix.det augmentedMatrix

def noFixedQuadraticContraction_claim11355 : Prop :=
  quadraticContractionNoGo ∧
    fourPrimeDeterminant = (48669310998387105708039956586777600000 : ℂ) ∧
    fourPrimeDeterminant ≠ 0

def fitsThreePrimes (c₀ c₁ c₂ : ℂ) : Prop :=
  quadraticContraction c₀ c₁ c₂ 2 = 2 ∧
    quadraticContraction c₀ c₁ c₂ 3 = 2 ∧
    quadraticContraction c₀ c₁ c₂ 5 = 2

def fittedC₀ : ℂ :=
  (262635059 : ℂ) / 1491421789266624

def fittedC₁ : ℂ :=
  (-1101802004517563 : ℂ) / 536911844135984640

def fittedC₂ : ℂ :=
  (55571407161610561 : ℂ) / 8013609613969920

def fittedPrimeSevenValue : ℂ :=
  (629718343337740616 : ℂ) / 1641835691841933

def fittedPrimeSevenGap : ℂ :=
  (626434671954056750 : ℂ) / 1641835691841933

def fittedPrimeSevenGapQ : ℚ :=
  (626434671954056750 : ℚ) / 1641835691841933

def uniqueThreePrimeFit_claim11356 : Prop :=
  (∃ c₀ c₁ c₂ : ℂ,
    fitsThreePrimes c₀ c₁ c₂ ∧
      c₀ = fittedC₀ ∧ c₁ = fittedC₁ ∧ c₂ = fittedC₂ ∧
      ∀ d₀ d₁ d₂ : ℂ,
        fitsThreePrimes d₀ d₁ d₂ →
          d₀ = c₀ ∧ d₁ = c₁ ∧ d₂ = c₂) ∧
    quadraticContraction fittedC₀ fittedC₁ fittedC₂ 7 = fittedPrimeSevenValue ∧
    fittedPrimeSevenValue - 2 = fittedPrimeSevenGap ∧
    0 < fittedPrimeSevenGapQ

def deltaThroughTwo : Polynomial ℤ :=
  Polynomial.X - 24 * Polynomial.X ^ 2

def e14ThroughOne : Polynomial ℤ :=
  1 - 24 * Polynomial.X

/-- The supplied exterior first Serre jet formula, retained through the needed degree. -/
def exteriorFirstSerreJetThroughTwo : Polynomial ℤ :=
  deltaThroughTwo * e14ThroughOne

def exteriorFirstSerreJetCoefficientAtTwo : ℤ :=
  (exteriorFirstSerreJetThroughTwo).coeff 2

def harmonicRankinVacuumPrimeCoefficient (_p : ℕ) : ℚ :=
  2

def closedOrbitPrimeCoefficient (p : ℕ) : ℚ :=
  (p : ℚ) ^ 11 + 2 + 1 / (p : ℚ) ^ 11

def closedOrbitGap (p : ℕ) : ℚ :=
  ((p : ℚ) ^ 22 + 1) / (p : ℚ) ^ 11

def pssScalarPrimeCoefficient (p : ℕ) : ℚ :=
  1 + 1 / (p : ℚ)

def pssVacuumMinusGap (p : ℕ) : ℚ :=
  ((p : ℚ) - 1) / (p : ℚ)

def fourOperationValueLevelNoGo_claim11363 : Prop :=
  (exteriorFirstSerreJetCoefficientAtTwo = -48 ∧
      (exteriorFirstSerreJetCoefficientAtTwo : ℚ) ≠
        harmonicRankinVacuumPrimeCoefficient 2) ∧
    (quadraticContractionNoGo ∧
      fourPrimeDeterminant = (48669310998387105708039956586777600000 : ℂ) ∧
      fourPrimeDeterminant ≠ 0) ∧
    (∀ p : ℕ, Nat.Prime p →
      closedOrbitPrimeCoefficient p =
          (p : ℚ) ^ 11 + 2 + 1 / (p : ℚ) ^ 11 ∧
        closedOrbitPrimeCoefficient p - harmonicRankinVacuumPrimeCoefficient p =
          closedOrbitGap p ∧
        0 < closedOrbitGap p) ∧
    (∀ p : ℕ, Nat.Prime p →
      harmonicRankinVacuumPrimeCoefficient p - pssScalarPrimeCoefficient p =
          pssVacuumMinusGap p ∧
        0 < pssVacuumMinusGap p)

end

end MathlibPlus.Open.Research.FormalizationBatch11355
