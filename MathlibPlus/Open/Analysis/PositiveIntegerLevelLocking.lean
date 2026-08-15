import Mathlib

namespace MathlibPlus.Open.Analysis.PositiveIntegerLevelLocking

def xValue (lambda theta : ℕ → ℝ) (n : ℕ) : ℝ :=
  lambda n * theta n

def rapidPolynomialL1 (lambda theta : ℕ → ℝ) : Prop :=
  ∀ q : ℕ,
    Summable (fun n => |xValue lambda theta n| * (lambda n) ^ q)

def positiveIntegerLocks (lambda theta : ℕ → ℝ) : Prop :=
  ∀ k q : ℕ, 0 < k →
    HasSum
      (fun n =>
        Real.sinh ((k : ℝ) * xValue lambda theta n) * (lambda n) ^ q)
      0

def positiveIntegerLevelLockingMain : Prop :=
  ∀ (lambda theta : ℕ → ℝ),
    (∀ n : ℕ, 0 < lambda n) →
    (∀ ⦃i j : ℕ⦄, i ≠ j → lambda i ≠ lambda j) →
    rapidPolynomialL1 lambda theta →
    positiveIntegerLocks lambda theta →
    ∀ n : ℕ, theta n = 0

def increasingPrimeSequence (p : ℕ → ℕ) : Prop :=
  StrictMono p ∧
    (∀ n : ℕ, Nat.Prime (p n)) ∧
    (∀ r : ℕ, Nat.Prime r → ∃ n : ℕ, p n = r)

def primeRapidPolynomialL1 (p : ℕ → ℕ) (theta : ℕ → ℝ) : Prop :=
  ∀ q : ℕ,
    Summable
      (fun n =>
        |theta (p n)| * (Real.log (p n : ℝ)) ^ (q + 1))

def primeReflectedAtomLocks (p : ℕ → ℕ) (theta : ℕ → ℝ) : Prop :=
  ∀ k q : ℕ, 0 < k →
    HasSum
      (fun n =>
        Real.sinh
            ((k : ℝ) * (Real.log (p n : ℝ) * theta (p n))) *
          (Real.log (p n : ℝ)) ^ q)
      0

def primeReflectedAtomBalance : Prop :=
  ∀ (p : ℕ → ℕ) (theta : ℕ → ℝ),
    increasingPrimeSequence p →
    primeRapidPolynomialL1 p theta →
    primeReflectedAtomLocks p theta →
    ∀ n : ℕ, theta (p n) = 0

def positiveIntegerLevelLocking : Prop :=
  positiveIntegerLevelLockingMain ∧ primeReflectedAtomBalance

end MathlibPlus.Open.Analysis.PositiveIntegerLevelLocking
