import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.D0024

noncomputable section

private def nr2_hasComplexEigenvalue
    (B : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℂ) : Prop :=
  ∃ v : Fin 2 → ℂ,
    (∃ i, v i ≠ 0) ∧
      ∀ i, ∑ j : Fin 2, ((B i j : ℝ) : ℂ) * v j = lam * v i

private def nr2_euclideanPositive : Prop :=
  ∀ v : Fin 2 → ℝ, (∃ i, v i ≠ 0) → 0 < ∑ i, v i ^ 2

private def nr2_companionMinus : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = 0 then if j = 0 then 0 else -9 else if j = 0 then 1 else -7

private def nr2_positiveForm (H : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ v : Fin 2 → ℝ, (∃ i, v i ≠ 0) →
    0 < ∑ i, ∑ j, v i * H i j * v j)

/-- Claim 4560: the reciprocal roots of the displayed quadratic are unequal
in modulus and neither lies on the q=9 purity circle. -/
def claim4560_failureOfPurityCircle (α β : ℂ) : Prop :=
  α + β = (-7 : ℂ) ∧ α * β = (9 : ℂ) ∧
    ‖α‖ ≠ ‖β‖ ∧
    ‖α‖ ≠ 3 ∧ ‖β‖ ≠ 3

/-- Claim 4561: the formal genus-one-shaped zeta function has the displayed
numerator and denominator. -/
def claim4561_formalGenusOneShapedZeta
    (Z : ℂ → ℂ) : Prop :=
  ∀ u : ℂ,
    Z u = (1 + 7 * u + 9 * u ^ 2) / ((1 - u) * (1 - 9 * u))

/-- Claim 4563: the logarithmic point counts are positive integers with the
reciprocal-root formula. -/
def claim4563_positiveIntegralPointCountData
    (α β : ℂ) (N : ℕ → ℤ) : Prop :=
  α + β = (-7 : ℂ) ∧ α * β = (9 : ℂ) ∧
    ∀ n : ℕ, 1 ≤ n →
      0 < N n ∧
        ((N n : ℤ) : ℂ) =
          (1 : ℂ) + (9 : ℂ) ^ n - α ^ n - β ^ n

/-- Claim 4567: a positive ordinary ambient metric coexists with an off-circle
spectrum, so ambient positivity alone has no purity consequence. -/
def claim4567_ordinaryAmbientPositivityIsSpectrallyBlind : Prop :=
  ∃ (B : Matrix (Fin 2) (Fin 2) ℝ) (α β : ℂ),
    nr2_euclideanPositive ∧
    nr2_hasComplexEigenvalue B α ∧
    nr2_hasComplexEigenvalue B β ∧
    α + β = (-7 : ℂ) ∧ α * β = (9 : ℂ) ∧
    ‖α‖ ≠ ‖β‖ ∧
    ‖α‖ ≠ 3 ∧ ‖β‖ ≠ 3 ∧
    ¬ (∀ lam : ℂ, nr2_hasComplexEigenvalue B lam → ‖lam‖ = 3)

/-- Claim 4568: the positive-coefficient q=9 quadratic has positive integral
point counts and positive integral closed-point exponents, but no positive
Rosati/similitude form. -/
def claim4568_combinedPositiveEulerPurityCounterfeit : Prop :=
  let B : Matrix (Fin 2) (Fin 2) ℝ := nr2_companionMinus
  (0 < (1 : ℤ) ∧ 0 < (7 : ℤ) ∧ 0 < (9 : ℤ)) ∧
    ∃ (α β : ℂ) (N closed : ℕ → ℤ),
      α + β = (-7 : ℂ) ∧ α * β = (9 : ℂ) ∧
      nr2_hasComplexEigenvalue B α ∧
      nr2_hasComplexEigenvalue B β ∧
      ‖α‖ ≠ ‖β‖ ∧
      ‖α‖ ≠ 3 ∧ ‖β‖ ≠ 3 ∧
      (∀ n : ℕ, 1 ≤ n →
        0 < N n ∧
          ((N n : ℤ) : ℂ) =
            (1 : ℂ) + (9 : ℂ) ^ n - α ^ n - β ^ n) ∧
      (∀ n : ℕ, 1 ≤ n →
        0 < closed n ∧
          N n = Finset.sum (Nat.divisors n) (fun d => (d : ℤ) * closed d)) ∧
      ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℝ,
        nr2_positiveForm H ∧
          (Matrix.transpose B * H * B = (9 : ℝ) • H)

end

end MathlibPlus.Open.NewResearch2.D0024
