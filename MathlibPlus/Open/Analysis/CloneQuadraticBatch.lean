import Mathlib

namespace MathlibPlus.Open.Analysis.CloneQuadraticBatch

structure CloneMap (n r : ℕ) where
  classOf : Fin r → Fin n
  everyClass : Function.Surjective classOf

def classTotal {n r : ℕ} (π : CloneMap n r) (cloneRate : Fin r → ℝ)
    (i : Fin n) : ℝ :=
  ∑ j : Fin r, if π.classOf j = i then cloneRate j else 0

def positiveRateVector {n : ℕ} (rate : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, 0 < rate i

def cloneRateTotals {n r : ℕ} (π : CloneMap n r)
    (rate : Fin n → ℝ) (cloneRate : Fin r → ℝ) : Prop :=
  ∀ i : Fin n, rate i = classTotal π cloneRate i

def cloneMatrix {n r : ℕ} (π : CloneMap n r)
    (K : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun s t => K (π.classOf s) (π.classOf t)

def quadraticForm {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, x i * K i j * x j

def inverseRateDiagonalBound {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (rate : Fin n → ℝ) (k : ℝ) : Prop :=
  ∀ x : Fin n → ℝ,
    quadraticForm K x ≤ k * ∑ i : Fin n, x i ^ 2 / rate i

def CloneLoewnerEquivalence : Prop :=
  ∀ (n r : ℕ) (π : CloneMap n r)
    (K : Matrix (Fin n) (Fin n) ℝ)
    (rate : Fin n → ℝ) (cloneRate : Fin r → ℝ) (k : ℝ),
    positiveRateVector rate →
    positiveRateVector cloneRate →
    cloneRateTotals π rate cloneRate →
    (inverseRateDiagonalBound K rate k ↔
      inverseRateDiagonalBound (cloneMatrix π K) cloneRate k)

end MathlibPlus.Open.Analysis.CloneQuadraticBatch
