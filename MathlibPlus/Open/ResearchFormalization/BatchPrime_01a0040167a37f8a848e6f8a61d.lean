import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Half-density prime towers and their one-step anti-causal filters. -/

def primePowerHalf (p k : ℕ) : ℝ :=
  (p : ℝ) ^ ((k : ℝ) / 2)

def primeTowerTerm (p : ℕ) (k : ℕ) (t : ℝ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) /
      ((primePowerHalf p k : ℝ) : ℂ) *
    Complex.exp
      (-Complex.I * (k : ℂ) * (t : ℂ) * (Real.log (p : ℝ) : ℂ))

def primeTowerSeries (p : ℕ) (t : ℝ) : ℂ :=
  ∑' k : ℕ, if 1 ≤ k then primeTowerTerm p k t else 0

def primeTowerClosed (p : ℕ) (t : ℝ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) /
    ((Real.sqrt (p : ℝ) : ℂ) *
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) - 1)

def primeFilter (a : ℕ → ℂ) (p : ℕ) (t : ℝ) : ℂ :=
  a p / (Real.log (p : ℝ) : ℂ) *
    ((Real.sqrt (p : ℝ) : ℂ) *
        Complex.exp (Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) - 1)

def primeCancellation (P : Finset ℕ) (a : ℕ → ℂ) : Prop :=
  ∀ t : ℝ,
    (∀ p ∈ P, primeTowerSeries p t = primeTowerClosed p t) ∧
    (∀ p ∈ P, primeFilter a p t * primeTowerSeries p t = a p) ∧
    (∑ p ∈ P, primeFilter a p t * primeTowerSeries p t) = 0

def claim60020 : Prop :=
  ∀ (P : Finset ℕ),
    (∀ p ∈ P, Nat.Prime p) →
    ∀ (a : ℕ → ℂ), (∑ p ∈ P, a p) = 0 →
      primeCancellation P a ∧
        (P.card ≥ 2 →
          ∃ p q : ℕ,
            p ∈ P ∧ q ∈ P ∧ p ≠ q ∧
            ∃ a' : ℕ → ℂ,
              (∑ r ∈ P, a' r) = 0 ∧
              a' p = 1 ∧ a' q = -1 ∧
              (∀ r, r ∈ P → r ≠ p → r ≠ q → a' r = 0) ∧
              primeCancellation P a' ∧
              (∀ t : ℝ, primeFilter a' p t ≠ 0 ∧
                primeFilter a' q t ≠ 0))


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
