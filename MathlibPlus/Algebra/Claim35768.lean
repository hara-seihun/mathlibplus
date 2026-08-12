import MathlibPlus.Basic

namespace MathlibPlus.Algebra

open scoped BigOperators

/-!
Formalization of admitted claim 35768.  The source's integer interval
`1 ≤ d ≤ m` is represented by the definitionally equivalent `range m`
with summand index `d + 1`; the coefficient field is `ℝ`, as required by
negative powers in the source notation.
-/

/-- The two finite dyadic identities for every positive truncation. -/
theorem dyadicFiniteSums_claim35768 (m : ℕ) (_hm : 1 ≤ m) :
    (∑ d ∈ Finset.range m, ((1 : ℝ) / 2) ^ (d + 1)) =
        1 - ((1 : ℝ) / 2) ^ m ∧
      (∑ d ∈ Finset.range m, (d + 1 : ℝ) * ((1 : ℝ) / 2) ^ (d + 1)) =
        2 - (m + 2 : ℝ) * ((1 : ℝ) / 2) ^ m := by
  clear _hm
  constructor
  · induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        ring
  · induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, pow_succ]
        push_cast
        ring

end MathlibPlus.Algebra
