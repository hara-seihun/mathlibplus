import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Research

/-- The usual prime-counting function on real arguments, expressed by the floor. -/
def primePi923 (x : ℝ) : ℕ :=
  ((Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime).card

def primeUpperEightTerm923 (C x : ℝ) : ℝ :=
  let L := Real.log x
  x / L + x / L ^ 2 + 2 * x / L ^ 3 +
    6.024334 * x / L ^ 4 + 24.024334 * x / L ^ 5 +
    120.12167 * x / L ^ 6 + 720.73002 * x / L ^ 7 +
    C * x / L ^ 8

/-- Admitted Claim 923. -/
def claim923 : Prop :=
  ∀ x : ℝ, 1 < x →
    (primePi923 x : ℝ) < primeUpperEightTerm923 6097.16044 x

/-- Admitted Claim 924. -/
def claim924 : Prop :=
  ∀ x : ℝ, 1 < x →
    (primePi923 x : ℝ) < primeUpperEightTerm923 6097.2 x

/-- The standard Chebyshev psi function on real arguments. -/
def chebyshevPsi955 (t : ℝ) : ℝ :=
  Finset.sum (Finset.Icc 1 ⌊t⌋₊) (fun n => ArithmeticFunction.vonMangoldt n)

/-- Admitted Claim 955. -/
def claim955 : Prop :=
  ∀ t : ℝ, 2 < t →
    |chebyshevPsi955 t - t| / t <
      9.2202181 * (Real.log t) ^ (3 / 2 : ℝ) *
        Real.exp (-0.8476836 * Real.sqrt (Real.log t))

/-- The exact order-five coefficient in admitted Claim 940. -/
def B5_940 : ℝ :=
  252969215940000000000 / 1999999999996903

/-- Admitted Claim 940. -/
def claim940 : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    ∃ p : ℕ,
      Nat.Prime p ∧
        x < (p : ℝ) ∧
          (p : ℝ) ≤ x * (1 + B5_940 / Real.log x ^ 5)

end MathlibPlus.Open.Research
