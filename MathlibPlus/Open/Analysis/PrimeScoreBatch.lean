import Mathlib

namespace MathlibPlus.Open.Analysis

/-- The usual prime-counting function, extended from naturals to reals by floor. -/
noncomputable def primeCountingReal (x : ℝ) : ℕ := Nat.primeCounting ⌊x⌋₊

/-- Axler's score and the denominator occurring in the coefficient bound. -/
noncomputable def B (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / (primeCountingReal x : ℝ))

noncomputable def D (c x : ℝ) : ℝ := Real.log x - 1 - c / Real.log x

/-- A point at which the prime-counting function can jump. -/
def isPrimePoint (x : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ (p : ℝ) = x

/-- No prime point lies in the open interval. -/
def isPrimeFree (a b : ℝ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(a < (p : ℝ) ∧ (p : ℝ) < b)

/-- `B x` is a strict new record relative to the starting endpoint `s`. -/
def isNewMaximumAfter (s x : ℝ) : Prop :=
  s < x ∧ ∀ y : ℝ, y ∈ Set.Ico s x → B y < B x

/--
Claim 1315.  The score has the displayed derivative wherever the
prime-counting function is constant on a prime-free interval; the global
`π(x) ≤ x/2` estimate gives the stated negative derivative bound, hence strict
monotonic decrease there and the record-maxima consequence.
-/
def claim1315 : Prop :=
  (∀ x : ℝ, 9 ≤ x → (primeCountingReal x : ℝ) ≤ x / 2) ∧
  (∀ (a b : ℝ) (n : ℕ),
    9 ≤ a → a ≤ b →
    (∀ x : ℝ, x ∈ Set.Ioo a b → primeCountingReal x = n) →
    isPrimeFree a b →
    (∀ x : ℝ, x ∈ Set.Ioo a b →
      HasDerivAt B
        ((2 * Real.log x - 1) / x - (Real.log x + 1) / (n : ℝ)) x) ∧
    (∀ x : ℝ, x ∈ Set.Ioo a b →
      ((2 * Real.log x - 1) / x - (Real.log x + 1) / (n : ℝ)) ≤ -3 / x) ∧
    (∀ x : ℝ, x ∈ Set.Ioo a b →
      ((2 * Real.log x - 1) / x - (Real.log x + 1) / (n : ℝ)) < 0) ∧
    (∀ x y : ℝ, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b → x < y → B y < B x)) ∧
  (∀ s x : ℝ, 9 ≤ s → isNewMaximumAfter s x → isPrimePoint x)

/--
Claim 1318.  The supplied decimal displays are retained as decimal-prefix
intervals: the value lies between the displayed truncation and the next unit
in its last displayed place.
-/
def claim1318 : Prop :=
  let x₀ : ℕ := 42575222481
  let n₀ : ℕ := 1817311115
  let score₀ : ℝ :=
    (11490003091852194519030898606008869613277 : ℝ) / (10 : ℝ) ^ 40
  let excess₀ : ℝ :=
    (97995437480881739846 : ℝ) / (10 : ℝ) ^ 20
  let x : ℝ := x₀
  let scoreExcess : ℝ :=
    (primeCountingReal x : ℝ) - x / D ((1149 : ℝ) / 1000) x
  primeCountingReal x = n₀ ∧
    ¬Nat.Prime x₀ ∧
    score₀ ≤ B x ∧ B x < score₀ + 1 / (10 : ℝ) ^ 40 ∧
    B x > (1149 : ℝ) / 1000 ∧
    excess₀ ≤ scoreExcess ∧ scoreExcess < excess₀ + 1 / (10 : ℝ) ^ 20 ∧
    scoreExcess > 0 ∧
    ¬(∀ y : ℝ, x ≤ y →
      (primeCountingReal y : ℝ) ≤ y / D ((1149 : ℝ) / 1000) y) ∧
    primeCountingReal ((x₀ - 1 : ℕ) : ℝ) = primeCountingReal x

end MathlibPlus.Open.Analysis
