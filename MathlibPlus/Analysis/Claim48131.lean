import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

open Polynomial

namespace MathlibPlus.Analysis

/--
Claim 48131 (R-3577.1): exact rational data at the rank-four zero-support
boundary.  The polynomial is normalized by scalar multiplication with
`1 / 2097152`, so the displayed coefficient is an ordinary coefficient in
`ℚ[X]`, not Euclidean polynomial division.
-/
theorem claim48131_rankFourBoundary :
    let F : ℚ[X] :=
      C (1 / 2097152) *
        ((1 + X) * (479249 * X ^ 3 - 2029584 * X ^ 2 - 546816 * X + 2097152))
    eval 0 F = 1 ∧ coeff F 2 = -161025 / 131072 := by
  dsimp
  constructor
  · norm_num [eval_mul]
  · have hexpand :
        ((1 + X) * (479249 * X ^ 3 - 2029584 * X ^ 2 - 546816 * X + 2097152) : ℚ[X]) =
          479249 * X ^ 4 - 1550335 * X ^ 3 - 2576400 * X ^ 2 +
            1550336 * X + 2097152 := by
        ring
    rw [hexpand]
    norm_num [coeff_C_mul, coeff_add, coeff_sub, coeff_X_pow, coeff_X]

end MathlibPlus.Analysis
