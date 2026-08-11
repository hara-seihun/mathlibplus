import Mathlib

open Polynomial

namespace MathlibPlus.Algebra

/-!
# First branch-polynomial coefficients

The congruence records the precise polynomial part of admitted claim 5601.  The
informal "degree" and "quadratic-star" channels are represented by the
coefficients of `X` and `X ^ 2`; no additional channel definitions are supplied
by the source claim.
-/

/-- Claim 5601: the first three coefficients of `(1 + X)^m` are the first two
binomial divided-power coefficients, equivalently the displayed congruence
modulo `X ^ 3`. -/
theorem branchPolynomial_mod_X3 (m : ℕ) :
    X ^ 3 ∣
      (1 + X) ^ m -
        (1 + C (m : ℤ) * X + C (m.choose 2 : ℤ) * X ^ 2) := by
  rw [X_pow_dvd_iff]
  intro d hd
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hd' with rfl | rfl | rfl <;>
    simp [coeff_sub, coeff_one_add_X_pow, coeff_one]

end MathlibPlus.Algebra
