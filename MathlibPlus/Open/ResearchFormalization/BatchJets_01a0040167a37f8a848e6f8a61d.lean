import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Jet annihilation for a finite exponential-polynomial carrier. -/

def iteratedDerivative (k : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (deriv^[k]) f

def exponentialPolynomial (R : ℕ) (c : Fin R → ℂ) (x : ℝ) : ℂ :=
  ∑ r : Fin R,
    c r * Complex.exp
      (-(Complex.I / 2) *
        (Real.log (((r.val + 1 : ℕ) : ℝ)) : ℂ) * (x : ℂ))

def nondegenerateRealInterval (I : Set ℝ) : Prop :=
  Set.OrdConnected I ∧ ∃ x y : ℝ, x ∈ I ∧ y ∈ I ∧ x < y

def claim58127 : Prop :=
  ∀ (I : Set ℝ), nondegenerateRealInterval I →
    ∀ (R : ℕ), 1 ≤ R →
      ∀ (m : ℕ) (x : Fin m → ℝ) (q : Fin m → ℕ),
        (∀ j : Fin m, x j ∈ I) →
        R > ∑ j : Fin m, (q j + 1) →
          ∃ c : Fin R → ℂ,
            c ≠ 0 ∧
              (∀ (j : Fin m) (k : ℕ), k ≤ q j →
                iteratedDerivative k (exponentialPolynomial R c) (x j) = 0) ∧
              ¬ (∀ y : ℝ, y ∈ I → exponentialPolynomial R c y = 0)


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
