import Mathlib

set_option autoImplicit false

namespace MathlibPlus.Open.R3406

/-- The number of positive divisors, with the zero input given the empty count. -/
def divisorTau (n : ℕ) : ℕ :=
  (Finset.filter (fun d : ℕ => d ∣ n) (Finset.Icc 1 n)).card

def Q3406Budget (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → divisorTau (n - k) ≤ k + 2

def FirstPrimeBranch (n s : ℕ) : Prop :=
  n = 8 * s + 8 ∧
    Nat.Prime s ∧ Nat.Prime (2 * s + 1) ∧
    Nat.Prime (4 * s + 3) ∧ Nat.Prime (8 * s + 7)

def SecondPrimeBranch (n s : ℕ) : Prop :=
  n = 16 * s + 8 ∧
    Nat.Prime s ∧ Nat.Prime (4 * s + 1) ∧
    Nat.Prime (8 * s + 3) ∧ Nat.Prime (16 * s + 7)

/-- The necessary four-prime reduction, without asserting existence in either family. -/
def FourPrimeGate : Prop :=
  ∀ n : ℕ, 24 < n → Q3406Budget n →
    (∃ s, FirstPrimeBranch n s) ∨ (∃ s, SecondPrimeBranch n s)

end MathlibPlus.Open.R3406
