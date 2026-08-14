import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch

/-
The packet's Newton normalization is used as the definition of the nested
forward divided difference at the equally spaced nodes a, a + 1, ... .
-/
def iteratedForwardDifference (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, t => f t
  | n + 1, t =>
      iteratedForwardDifference (fun u => f (u + 1) - f u) n t

def risingFactorial (x : ℝ) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) (fun k => x + (k : ℝ))

noncomputable def dividedDifference (a : ℝ) (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  iteratedForwardDifference (fun n => f (a + (n : ℝ))) m 0 /
    (m.factorial : ℝ)

def dualPolynomial (a : ℝ) (e : ℕ) (x : ℝ) : ℝ :=
  Finset.prod (Finset.range e)
    (fun n => x ^ 2 - (a + (n : ℝ)) ^ 2)

def dualPolynomialDifference (a : ℝ) (e : ℕ) (x : ℝ) : ℝ :=
  dualPolynomial a e x - dualPolynomial a e 0

/-- Claim 1158: the all-order dual divided-difference identity. -/
def allOrderDualDividedDifferenceIdentity : Prop :=
  (∀ (a : ℝ) (e s : ℕ),
      0 < e →
        ((0 ≤ s ∧ s ≤ e) →
          dividedDifference a (e + s) (dualPolynomialDifference a e) =
              (1 / (s.factorial : ℝ)) *
                iteratedForwardDifference
                  (fun t =>
                    risingFactorial
                      (2 * a + (e : ℝ) + (t : ℝ)) e) s 0 ∧
            (1 / (s.factorial : ℝ)) *
                iteratedForwardDifference
                  (fun t =>
                    risingFactorial
                      (2 * a + (e : ℝ) + (t : ℝ)) e) s 0 =
              (Nat.choose e s : ℝ) *
                risingFactorial
                  (2 * a + (e : ℝ) + (s : ℝ)) (e - s)) ∧
        (e < s →
          dividedDifference a (e + s) (dualPolynomialDifference a e) = 0)) ∧
    (∀ (a : ℝ) (e : ℕ),
      0 < e →
        dividedDifference a e (dualPolynomialDifference a e) =
            risingFactorial (2 * a + (e : ℝ)) e ∧
        dividedDifference a (e + 1) (dualPolynomialDifference a e) =
            (e : ℝ) * risingFactorial
              (2 * a + (e : ℝ) + 1) (e - 1) ∧
        dividedDifference a (e + 2) (dualPolynomialDifference a e) =
            (Nat.choose e 2 : ℝ) * risingFactorial
              (2 * a + (e : ℝ) + 2) (e - 2)) ∧
    (∀ (a : ℝ),
      dividedDifference a 3 (dualPolynomialDifference a 1) = 0)

/-!
The reviewed repair context for Claim 1166 fixes the prime-counting carrier to
Nat.primeCounting ⌊x⌋₊ and uses the strict real inequality without adding a
separate denominator-domain hypothesis.
-/
noncomputable def table8PrimeCount (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ)

noncomputable def table8Score (x : ℝ) : ℝ :=
  Real.log x - x / table8PrimeCount x

noncomputable def table8Alpha (x₀ : ℝ) : ℝ :=
  sSup (table8Score '' Set.Ici x₀)

/-- The suffix maximum relation represented by the alpha value. -/
def table8SuffixMaximum (x₀ : ℝ) : Prop :=
  IsGreatest (table8Score '' Set.Ici x₀) (table8Alpha x₀)

noncomputable def table8PredecessorThreshold (x₀ : ℝ) : ℝ :=
  table8Score (x₀ - 1)

/-- The strict Axler bound holds at every real point on the half-line. -/
def table8ValidFrom (c N : ℝ) : Prop :=
  ∀ x : ℝ, N ≤ x →
    table8PrimeCount x < x / (Real.log x - c)

/-- The valid integer starts have the stated least-start minimality. -/
def table8LeastIntegerStart (c : ℝ) (N : ℤ) : Prop :=
  table8ValidFrom c (N : ℝ) ∧
    ∀ M : ℤ, M < N → ¬ table8ValidFrom c (M : ℝ)

/--
Claim 1166: the named score, suffix maximum, predecessor threshold, and
integer-start predicates have their literal packet definitions.
-/
def table8ThresholdSuffixMaximumPredecessor : Prop :=
  (∀ (x₀ : ℝ),
      table8Score x₀ =
        Real.log x₀ - x₀ / table8PrimeCount x₀ ∧
      table8Alpha x₀ = sSup (table8Score '' Set.Ici x₀) ∧
      table8PredecessorThreshold x₀ = table8Score (x₀ - 1)) ∧
    (∀ (c N : ℝ),
      table8ValidFrom c N ↔
        ∀ x : ℝ, N ≤ x →
          table8PrimeCount x < x / (Real.log x - c)) ∧
    (∀ (c : ℝ) (N : ℤ),
      table8LeastIntegerStart c N ↔
        (table8ValidFrom c (N : ℝ) ∧
          ∀ M : ℤ, M < N → ¬ table8ValidFrom c (M : ℝ)))

end MathlibPlus.Open.FormalizationBatch
