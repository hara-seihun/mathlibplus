import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Arithmetic.IntegerFactorization

/-! Formalization of admitted claim 42939. -/

/-- The exact factorization recorded in claim 42939. -/
theorem factorization_160626866400 :
    (160626866400 : ℕ) =
      2 ^ 5 * 3 ^ 3 * 5 ^ 2 * 7 * 11 * 13 * 17 * 19 * 23 := by
  norm_num

end MathlibPlus.Arithmetic.IntegerFactorization
