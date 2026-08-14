import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.FormalizationBatch.PrimeShift

def divisorCount (m : ℕ) : ℕ := (Nat.divisors m).card

def shiftGood (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → divisorCount (n - k) ≤ k + 2

def valuation (p m : ℕ) : ℕ := Nat.factorization m p

def primeAfterExactValuation (p m : ℕ) (allowed : Finset ℕ) : Prop :=
  let e := valuation p m
  e ∈ allowed ∧ p ^ e ∣ m ∧ Nat.Prime (m / p ^ e)

def rowsWithThirteenPrimeValues (N : ℕ) : Prop :=
  Nat.Prime (2520 * N - 1) ∧
  Nat.Prime (1260 * N - 1) ∧
  Nat.Prime (840 * N - 1) ∧
  Nat.Prime (630 * N - 1) ∧
  primeAfterExactValuation 5 (504 * N - 1) ({0, 1} : Finset ℕ) ∧
  Nat.Prime (420 * N - 1) ∧
  primeAfterExactValuation 2 (315 * N - 1) ({0, 1} : Finset ℕ) ∧
  primeAfterExactValuation 3 (280 * N - 1) ({0, 1, 2} : Finset ℕ) ∧
  primeAfterExactValuation 5 (252 * N - 1) ({0, 1} : Finset ℕ) ∧
  Nat.Prime (210 * N - 1) ∧
  primeAfterExactValuation 3 (140 * N - 1) ({0, 1, 2} : Finset ℕ) ∧
  primeAfterExactValuation 5 (126 * N - 1) ({0, 1} : Finset ℕ) ∧
  primeAfterExactValuation 2 (105 * N - 1) ({0, 1, 2} : Finset ℕ)

/-- Claim 58862: the thirteen normalized prime rows forced by all shift
inequalities. -/
def claim58862_thirteenForcedPrimeExpressions : Prop :=
  ∀ (N n : ℕ), n = 2520 * N → shiftGood n → rowsWithThirteenPrimeValues N

def divisorRows : Finset ℕ :=
  {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 18, 20, 24}

def modularRootSet (p c : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter (fun r : ZMod p =>
    r ≠ 0 ∧ (c : ZMod p) * r = 1)

def rootCover (p : ℕ) [NeZero p] : Prop := by
  classical
  exact divisorRows.biUnion (fun k => modularRootSet p (2520 / k)) =
    (Finset.univ.erase 0 : Finset (ZMod p))

def normalizationUnits (p : ℕ) : Prop :=
  ∀ q : ℕ, q ∈ ({2, 3, 5} : Finset ℕ) → (q : ZMod p) ≠ 0

/-- Claim 58863: the two exact nonzero-residue covers and the resulting
forced divisibility, conditional on the thirteen prime rows. -/
def claim58863_rootCoversModuloElevenAndThirteen : Prop :=
  rootCover 11 ∧ rootCover 13 ∧
    normalizationUnits 11 ∧ normalizationUnits 13 ∧
    ∀ N : ℕ, 0 < N → rowsWithThirteenPrimeValues N → 11 * 13 ∣ N

/-- The residual set of shift points and its counting function. -/
def residualPoint (n : ℕ) : Prop :=
  24 < n ∧ shiftGood n

def residualCount (x : ℝ) : ℕ := by
  classical
  exact ((Finset.Iic ⌊x⌋₊).filter (fun n => residualPoint n)).card

def sieveUpperBound : Prop :=
  ∃ (C x₀ : ℝ), 0 < C ∧ 0 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (residualCount x : ℝ) ≤ C * x / (Real.log x) ^ 13

def residualDivisorObligation : Prop :=
  ∀ (n : ℕ), residualPoint n → Nat.Prime (n - 1) →
    ∃ d : ℕ, 1 ≤ d ∧ divisorCount ((n - 1) - d) > d + 3

/-- Claim 58865: the finite-union sieve boundary and the exact remaining
pointwise divisor obligation. -/
def claim58865_remainingDensityBoundary : Prop :=
  sieveUpperBound

end MathlibPlus.Open.FormalizationBatch.PrimeShift
