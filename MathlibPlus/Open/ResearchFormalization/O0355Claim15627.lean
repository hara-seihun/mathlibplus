import Mathlib

open Filter Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0355Claim15627

noncomputable section

abbrev CyclotomicIndex := Fin 5 →₀ ℕ
abbrev PrimeIndex := {p : ℕ // Nat.Prime p}
abbrev Series := MvPowerSeries (Fin 5) ℤ

def totalDegree (n : CyclotomicIndex) : ℕ :=
  ∑ j : Fin 5, n j

noncomputable def cyclotomicFactorInverse (n : CyclotomicIndex) : Series :=
  MvPowerSeries.invOfUnit
    (1 - MvPowerSeries.monomial n 1) (1 : ℤˣ)

def integerPower (n : CyclotomicIndex) : ℤ → Series
  | Int.ofNat k => (1 - MvPowerSeries.monomial n 1) ^ k
  | Int.negSucc k => cyclotomicFactorInverse n ^ (k + 1)

def finiteCyclotomicProduct
    (c : CyclotomicIndex → ℤ) (F : Finset CyclotomicIndex) : Series :=
  ∏ n ∈ F, integerPower n (c n)

def formalDenominator (m : ℕ) : Series :=
  let X := MvPowerSeries.monomial (Finsupp.single (0 : Fin 5) 1) 1
  let U : Fin 4 → Series := fun j =>
    MvPowerSeries.monomial (Finsupp.single j.succ 1) 1
  1 - (1 - MvPowerSeries.C (m : ℤ) * ∑ j : Fin 4, U j) * X

noncomputable def formalDenominatorInverse (m : ℕ) : Series :=
  MvPowerSeries.invOfUnit (formalDenominator m) (1 : ℤˣ)

noncomputable def integralW (m : ℕ) : Series :=
  let X := MvPowerSeries.monomial (Finsupp.single (0 : Fin 5) 1) 1
  (1 - X) * formalDenominatorInverse m

def formalCyclotomicFactorization
    (m : ℕ) (c : CyclotomicIndex → ℤ) : Prop :=
  (formalDenominator m * formalDenominatorInverse m = 1 ∧
      formalDenominatorInverse m * formalDenominator m = 1) ∧
    (∀ j : Fin 4,
      c (Finsupp.single (0 : Fin 5) 1 + Finsupp.single j.succ 1) = (m : ℤ)) ∧
    (∀ n, c n ≠ 0 →
      1 ≤ n 0 ∧ 1 ≤ ∑ j : Fin 4, n j.succ ∧
      (1 - MvPowerSeries.monomial n 1) * cyclotomicFactorInverse n = 1 ∧
      cyclotomicFactorInverse n * (1 - MvPowerSeries.monomial n 1) = 1) ∧
    ∀ d : CyclotomicIndex, ∃ F : Finset CyclotomicIndex,
      (∀ n, n ∈ F ↔ c n ≠ 0 ∧
        1 ≤ n 0 ∧ 1 ≤ ∑ j : Fin 4, n j.succ ∧
        totalDegree n ≤ totalDegree d) ∧
      MvPowerSeries.coeff d (integralW m) =
        MvPowerSeries.coeff d (finiteCyclotomicProduct c F)

def eta (α τ : ℝ) : ℂ :=
  (α : ℂ) - (τ : ℂ) * Complex.I

def plantedQuartet (α τ : ℝ) : Fin 4 → ℂ :=
  ![eta α τ, starRingEnd ℂ (eta α τ), 1 - eta α τ,
    starRingEnd ℂ (1 - eta α τ)]

def supportedIndex (n : CyclotomicIndex) : Prop :=
  1 ≤ n 0 ∧ 1 ≤ ∑ j : Fin 4, n j.succ

def primaryIndex (j : Fin 4) : CyclotomicIndex :=
  Finsupp.single (0 : Fin 5) 1 + Finsupp.single j.succ 1

def shiftedZetaArgument
    (α τ : ℝ) (n : CyclotomicIndex) (s : ℂ) : ℂ :=
  (n 0 : ℂ) * s +
    ∑ j : Fin 4, (n j.succ : ℂ) * plantedQuartet α τ j

def primeInversePower (p : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (p : ℝ) : ℂ))

noncomputable def finiteEulerCorrection
    (a : ℕ → ℝ) (Y : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (Finset.range (2 * Y + 1)).filter Nat.Prime,
    (1 - primeInversePower p s) /
      (1 - (a p : ℂ) * primeInversePower p s)

noncomputable def degreeOneEulerProduct
    (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∏' p : PrimeIndex,
    (1 - (a p.1 : ℂ) * primeInversePower p.1 s)⁻¹

def basePrimeValue (m : ℕ) (α τ : ℝ) (p : ℕ) : ℝ :=
  1 - 2 * (m : ℝ) *
    (Real.rpow (p : ℝ) (-α) + Real.rpow (p : ℝ) (-(1 - α))) *
      Real.cos (τ * Real.log (p : ℝ))

def positiveCompletelyMultiplicative (a : ℕ → ℝ) : Prop :=
  a 1 = 1 ∧
    (∀ r s : ℕ, a (r * s) = a r * a s) ∧
    (∀ n : ℕ, 0 < a n)

/-- The local continuation data at one quartet target, including the primary
factor indexed by the reflected quartet entry. -/
def localExactOrderData
    (m : ℕ) (α τ : ℝ) (Y : ℕ) (a : ℕ → ℝ) (L : ℂ → ℂ)
    (s₀ : ℂ) (j r : Fin 4) : Prop :=
  s₀ = plantedQuartet α τ j ∧
    plantedQuartet α τ r = 1 - s₀ ∧
      ∃ (c : CyclotomicIndex → ℤ)
        (S : Finset CyclotomicIndex) (G h : ℂ → ℂ),
        formalCyclotomicFactorization m c ∧
          (∀ n, c n ≠ 0 → supportedIndex n) ∧
          S.Nonempty ∧
          primaryIndex r ∈ S ∧
          c (primaryIndex r) = (m : ℤ) ∧
          (∀ s : ℂ,
            shiftedZetaArgument α τ (primaryIndex r) s =
              s + plantedQuartet α τ r) ∧
          (∀ n ∈ S, c n ≠ 0 ∧ supportedIndex n) ∧
          AnalyticAt ℂ G s₀ ∧ G s₀ ≠ 0 ∧
          AnalyticAt ℂ h s₀ ∧ h s₀ = 1 ∧
          riemannZeta s₀ ≠ 0 ∧
          finiteEulerCorrection a Y s₀ ≠ 0 ∧
          (∀ n ∈ S, n ≠ primaryIndex r →
            riemannZeta (shiftedZetaArgument α τ n s₀) ≠ 0) ∧
          (∀ᶠ s in 𝓝 s₀,
            s ≠ s₀ →
              (riemannZeta (s + plantedQuartet α τ r)) ^
                  (-(m : ℤ)) =
                (s - s₀) ^ m * h s) ∧
          (∀ᶠ s in 𝓝 s₀,
            s ≠ s₀ →
              L s =
                G s * riemannZeta s * finiteEulerCorrection a Y s *
                  (∏ n ∈ S,
                    (riemannZeta (shiftedZetaArgument α τ n s)) ^
                      (-(c n : ℤ)))) ∧
          AnalyticAt ℂ L s₀ ∧
          L s₀ = 0 ∧
          meromorphicOrderAt L s₀ = (m : WithTop ℤ)

/-- Claim 15627: the corrected degree-one Euler products have a fixed
symmetric quartet of exact order-`m` zeros outside one countable exceptional
set of heights.  The local factor at a target uses the reflected quartet
entry, so its primary shifted zeta argument is one at that target. -/
def claim15627 : Prop :=
  ∀ (m : ℕ) (α : ℝ),
    1 ≤ m → Irrational α → 0 < α → α < (1 : ℝ) / 2 →
      ∃ E : Set ℝ,
        E.Countable ∧ E ⊆ Set.Ioi (0 : ℝ) ∧
          ∀ τ : ℝ, 0 < τ → τ ∉ E →
            ∃ C : ℝ, 0 ≤ C ∧
              ∃ Y₀ : ℕ, ∀ Y : ℕ, Y₀ ≤ Y →
                ∃ (a : ℕ → ℝ) (L : ℂ → ℂ) (u : ℝ),
                  |u| ≤ C * Real.rpow (Y : ℝ) (-α) ∧
                  positiveCompletelyMultiplicative a ∧
                  (∀ p : PrimeIndex, p.1 ≤ Y → a p.1 = 1) ∧
                  (∀ p : PrimeIndex, Y < p.1 → p.1 ≤ 2 * Y →
                    a p.1 = basePrimeValue m α τ p.1 + u) ∧
                  (∀ p : PrimeIndex, 2 * Y < p.1 →
                    a p.1 = basePrimeValue m α τ p.1) ∧
                  (∀ p : PrimeIndex, Y < p.1 →
                    (1 / 2 : ℝ) < a p.1 ∧ a p.1 < (3 / 2 : ℝ)) ∧
                  MeromorphicOn L {s : ℂ | 0 < s.re} ∧
                  (∀ s : ℂ, 1 < s.re →
                    L s = degreeOneEulerProduct a s) ∧
                  (∀ s₀ : ℂ,
                    (∃ j : Fin 4, s₀ = plantedQuartet α τ j) →
                      ∃ j r : Fin 4,
                        localExactOrderData m α τ Y a L s₀ j r)

end

end MathlibPlus.Open.ResearchFormalization.O0355Claim15627
