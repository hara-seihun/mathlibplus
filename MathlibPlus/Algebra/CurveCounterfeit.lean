import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.CurveCounterfeit

/-- The reciprocal quadratic `P₋(u) = 1 + 7u + 9u²` at `q = 9`. -/
def reciprocalPolynomial (u : ℝ) : ℝ :=
  1 + 7 * u + 9 * u ^ 2

/-- The smaller reciprocal characteristic root of `P₋`. -/
noncomputable def alpha : ℝ :=
  (-7 + Real.sqrt 13) / 2

/-- The larger-in-modulus reciprocal characteristic root of `P₋`. -/
noncomputable def beta : ℝ :=
  (-7 - Real.sqrt 13) / 2

/-- The formal rational zeta function attached to the counterfeit quadratic. -/
noncomputable def zetaFunction (u : ℝ) : ℝ :=
  reciprocalPolynomial u / ((1 - u) * (1 - 9 * u))

/-- The displayed point-count sequence of the counterfeit. -/
noncomputable def pointCount (n : ℕ) : ℝ :=
  (9 : ℝ) ^ n + 1 - (alpha ^ n + beta ^ n)

/-- The formal-power-series germ of the counterfeit zeta function. -/
noncomputable def zetaSeries : PowerSeries ℝ :=
  (1 + 7 * PowerSeries.X + 9 * PowerSeries.X ^ 2) *
    (1 - PowerSeries.X)⁻¹ * (1 - 9 * PowerSeries.X)⁻¹

/-- The ordinary generating series of the displayed positive-index point counts. -/
noncomputable def pointCountSeries : PowerSeries ℝ :=
  PowerSeries.mk fun n => pointCount (n + 1)

/-- The reciprocal equation and all exact characteristic-root assertions from the
counterfeit construction.  The normalized moduli use `sqrt 9 = 3`. -/
theorem reciprocalQuadraticIdentities :
    (∀ u : ℝ, u ≠ 0 →
      reciprocalPolynomial u =
        9 * u ^ 2 * reciprocalPolynomial (1 / (9 * u))) ∧
    alpha + beta = -7 ∧
    alpha * beta = 9 ∧
    |alpha| < 2 ∧
    |beta| < 6 ∧
    |alpha| / 3 ≠ |beta| / 3 := by
  have hsqrt_sq : (Real.sqrt 13) ^ 2 = 13 := by norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg _
  have hsqrt_pos : 0 < Real.sqrt 13 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_lt_four : Real.sqrt 13 < 4 := by nlinarith
  have halpha_neg : alpha < 0 := by
    rw [alpha]
    nlinarith
  have hbeta_neg : beta < 0 := by
    rw [beta]
    nlinarith
  constructor
  · intro u hu
    rw [reciprocalPolynomial, reciprocalPolynomial]
    field_simp
    ring
  constructor
  · rw [alpha, beta]
    ring
  constructor
  · rw [alpha, beta]
    nlinarith
  constructor
  · rw [abs_of_neg halpha_neg, alpha]
    nlinarith
  constructor
  · rw [abs_of_neg hbeta_neg, beta]
    nlinarith
  · rw [abs_of_neg halpha_neg, abs_of_neg hbeta_neg, alpha, beta]
    intro h
    nlinarith

end MathlibPlus.Algebra.CurveCounterfeit

namespace MathlibPlus.Open.Algebra.CurveCounterfeit

open MathlibPlus.Algebra.CurveCounterfeit

/-- Claim 256's full reciprocal positive-Euler counterfeit assertion.  The source's
rational reciprocity is stated on its natural domain `u ≠ 0`.  Integral Euler
exponents are represented by an integer-valued sequence satisfying the exact
Möbius relation at every positive index, together with uniqueness on those indices. -/
def reciprocalPositiveEulerCounterfeit : Prop :=
  (∀ u : ℝ, u ≠ 0 →
    reciprocalPolynomial u =
      9 * u ^ 2 * reciprocalPolynomial (1 / (9 * u))) ∧
  alpha + beta = -7 ∧
  alpha * beta = 9 ∧
  |alpha| < 2 ∧
  |beta| < 6 ∧
  |alpha| / 3 ≠ |beta| / 3 ∧
  (PowerSeries.derivative ℝ) zetaSeries = zetaSeries * pointCountSeries ∧
  ∃ B : ℕ → ℤ,
    (∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * (B n : ℝ) =
        ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℝ) * pointCount (n / d)) ∧
    ∀ C : ℕ → ℤ,
      (∀ n : ℕ, 1 ≤ n →
        (n : ℝ) * (C n : ℝ) =
          ∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) * pointCount (n / d)) →
      ∀ n : ℕ, 1 ≤ n → C n = B n

end MathlibPlus.Open.Algebra.CurveCounterfeit
