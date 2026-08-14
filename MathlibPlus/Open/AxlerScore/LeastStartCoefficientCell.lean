import Mathlib

namespace MathlibPlus.Open.AxlerScore

/-- The coefficient-dependent denominator from the admitted normalization. -/
noncomputable def coefficientDenominator (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

/-- The real extension of the prime-counting function used by the admitted score. -/
noncomputable def primeCountingReal (x : ℝ) : ℝ :=
  (Nat.primeCounting (Nat.floor x) : ℝ)

/-- The admitted pole-cancelled prime-counting score B. -/
noncomputable def score (x : ℝ) : ℝ :=
  Real.log x * (Real.log x - 1 - x / primeCountingReal x)

/-- The admitted strict bound validity predicate from a real start. -/
noncomputable def validFrom (c X : ℝ) : Prop :=
  ∀ x : ℝ, X ≤ x →
    primeCountingReal x < x / coefficientDenominator c x

/-- Validity from a natural start, with no smaller natural start valid. -/
noncomputable def leastIntegerStart (c : ℝ) (N : ℕ) : Prop :=
  validFrom c (N : ℝ) ∧
    ∀ M : ℕ, M < N → ¬ validFrom c (M : ℝ)

/-- Attainment of a maximum on the real suffix beginning at a natural N. -/
def attainedSuffixMaximum (B : ℝ → ℝ) (N : ℕ) (α : ℝ) : Prop :=
  ∃ x₀ : ℝ,
    (N : ℝ) ≤ x₀ ∧
      B x₀ = α ∧
        ∀ x : ℝ, (N : ℝ) ≤ x → B x ≤ α

/-- Strict decrease on the real interval [a,b]. -/
def strictlyDecreasingOn (B : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄, a ≤ x → x < y → y ≤ b → B y < B x

/-- Natural compositeness for the integer start. -/
def compositeNatural (N : ℕ) : Prop :=
  ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = N

/--
The admitted abstract least-start coefficient-cell lemma: under the stated
maximum, endpoint, monotonicity, compositeness, and denominator hypotheses,
the least integer start is exactly the half-open coefficient cell.
-/
def abstractLeastStartCoefficientCell : Prop :=
  ∀ (N : ℕ) (c α β : ℝ),
    9 ≤ N →
      compositeNatural N →
        attainedSuffixMaximum score N α →
          β = score ((N : ℝ) - 1) →
            strictlyDecreasingOn score ((N : ℝ) - 1) (N : ℝ) →
              (∀ x : ℝ, (N : ℝ) - 1 ≤ x →
                0 < coefficientDenominator c x) →
                leastIntegerStart c N ↔ α < c ∧ c ≤ β

end MathlibPlus.Open.AxlerScore
