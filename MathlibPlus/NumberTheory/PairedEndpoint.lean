import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MathlibPlus.NumberTheory.PairedEndpoint

/-- Claim 24493: for the source's monic degree-28 integral trace polynomial,
positive endpoint values with the displayed mod-four congruence have product
at least three. -/
theorem positivePairedEndpoints_product_ge_three
    (ell : Polynomial ℤ)
    (_hmonic : ell.Monic)
    (_hdegree : ell.natDegree = 28)
    (hplus : 0 < -ell.eval 2)
    (hminus : 0 < ell.eval (-2))
    (hmod : ((-ell.eval 2) + ell.eval (-2)) % 4 = 0) :
    3 ≤ (-ell.eval 2) * ell.eval (-2) := by
  let a : ℤ := -ell.eval 2
  let b : ℤ := ell.eval (-2)
  have ha : 0 < a := by simpa [a] using hplus
  have hb : 0 < b := by simpa [b] using hminus
  have hab : (a + b) % 4 = 0 := by simpa [a, b] using hmod
  change 3 ≤ a * b
  by_cases hsmall : a < 3
  · interval_cases a <;> norm_num at * <;> omega
  · have ha3 : 3 ≤ a := by omega
    have hb1 : 1 ≤ b := by omega
    have hmul : a * 1 ≤ a * b :=
      mul_le_mul_of_nonneg_left hb1 (by omega)
    have hbase : 3 ≤ a * 1 := by simpa using ha3
    exact hbase.trans hmul

end MathlibPlus.NumberTheory.PairedEndpoint
