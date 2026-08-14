import Mathlib

namespace MathlibPlus.Open.Research.AdmittedBatchR0149

-- These are the coefficient sequences of the three displayed cosh germs:
-- cosh(a * sqrt(z)) has coefficient a^(2*n)/(2*n)! at z^n.
private def separated_h (n : ℕ) : ℚ :=
  ((4 / 5 : ℚ) ^ (2 * n) + (3 / 2 : ℚ) ^ (2 * n)) /
    (Nat.factorial (2 * n) : ℚ)

private def separated_e (n : ℕ) : ℚ :=
  (3 / 10 : ℚ) ^ (2 * n) / (Nat.factorial (2 * n) : ℚ)

-- B = E + 2 z E' coefficientwise.
private def separated_b (n : ℕ) : ℚ :=
  (1 + 2 * n) * separated_e n

private noncomputable def separated_quotient (n : ℕ) : ℚ :=
  PowerSeries.coeff n
    (PowerSeries.mk separated_b * PowerSeries.inv (PowerSeries.mk separated_h))

private def separated_hankel (r : ℕ → ℚ) (N : ℕ) : Matrix (Fin N) (Fin N) ℚ :=
  fun i j => r (i.val + j.val + 1)

private def separated_pivot (r : ℕ → ℚ) (n : ℕ) : ℚ :=
  Matrix.det (separated_hankel r (n + 1)) /
    Matrix.det (separated_hankel r n)

/-- The stated initial pivot word and second leading minor for the quotient B/H. -/
def euler_cosh_separated_support_counterexample : Prop :=
  separated_pivot separated_quotient 0 = -(47 : ℚ) / 160 ∧
  separated_pivot separated_quotient 0 < 0 ∧
  separated_pivot separated_quotient 1 < 0 ∧
  separated_pivot separated_quotient 2 > 0 ∧
  separated_pivot separated_quotient 3 < 0 ∧
  separated_pivot separated_quotient 4 > 0 ∧
  Matrix.det (separated_hankel separated_quotient 2) =
    (35400007 : ℚ) / 307200000000 ∧
  ¬ separated_pivot separated_quotient 1 > 0

end MathlibPlus.Open.Research.AdmittedBatchR0149
