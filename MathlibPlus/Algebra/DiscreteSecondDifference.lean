import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

namespace MathlibPlus.Algebra

open BigOperators

private lemma sum_secondDifference {R : Type*} [AddCommGroup R]
    (F : ℕ → R) (n j : ℕ) :
    ∑ q ∈ Finset.range j,
        ((F (n + q + 2) - F (n + q + 1)) - (F (n + q + 1) - F (n + q))) =
      (F (n + j + 1) - F (n + j)) -
        (F (n + 1) - F n) := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      have harg : n + (j + 2) = n + (j + 1) + 1 := by omega
      rw [← harg]
      abel

/-- Exact summation of the discrete second difference.

The displayed range is the source sum with the source index `q` reindexed as
`q = q' + 1`; thus its terms are precisely the terms for `1 ≤ q < k`.
The source writes only "integer `k ≥ 0`" and does not specify the domain of
`F` or `n`; this faithful sequence form uses natural-number indices and an
arbitrary additive-commutative-group codomain. -/
theorem exactDiscreteSecondDifferenceSummation {R : Type*} [AddCommGroup R]
    (F : ℕ → R) (n k : ℕ) :
    F (n + k) - F n - k • (F (n + 1) - F n) =
      let Δ : ℕ → R := fun q =>
        (F (n + q + 2) - F (n + q + 1)) - (F (n + q + 1) - F (n + q))
      ∑ q ∈ Finset.range (k - 1), (k - (q + 1)) • Δ q := by
  dsimp
  cases k with
  | zero => simp
  | succ j =>
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      induction j with
      | zero =>
          simp
          abel
      | succ j ih =>
          rw [Finset.sum_range_succ]
          have hcoef : ∀ q ∈ Finset.range j, j + 1 - q = (j - q) + 1 := by
            intro q hq
            have hq' : q < j := Finset.mem_range.1 hq
            omega
          have hsum := sum_secondDifference F n (j + 1)
          have hrewrite :
              (∑ q ∈ Finset.range j,
                  (j + 1 - q) •
                    ((F (n + q + 2) - F (n + q + 1)) -
                      (F (n + q + 1) - F (n + q)))) =
                ∑ q ∈ Finset.range j,
                  ((j - q) •
                      ((F (n + q + 2) - F (n + q + 1)) -
                        (F (n + q + 1) - F (n + q))) +
                    ((F (n + q + 2) - F (n + q + 1)) -
                      (F (n + q + 1) - F (n + q)))) := by
            apply Finset.sum_congr rfl
            intro q hq
            rw [hcoef q hq, add_nsmul]
            simp only [one_nsmul]
          have hstep :
              F (n + (j + 1 + 1)) - F n - (j + 1 + 1) • (F (n + 1) - F n) =
                (F (n + (j + 1)) - F n - (j + 1) • (F (n + 1) - F n)) +
                  ((F (n + j + 2) - F (n + j + 1)) -
                    (F (n + 1) - F n)) := by
            have harg : n + (j + 1 + 1) = n + j + 2 := by omega
            rw [harg]
            simp only [add_nsmul]
            abel
          have hj : j + 1 - j = 1 := by omega
          rw [hstep, ih, hrewrite, hj]
          simp only [one_nsmul]
          have hsum' :
              (∑ q ∈ Finset.range (j + 1),
                  ((F (n + q + 2) - F (n + q + 1)) -
                    (F (n + q + 1) - F (n + q)))) =
                (F (n + (j + 2)) - F (n + (j + 1))) -
                  (F (n + 1) - F n) := by
            convert hsum using 1 <;> congr 1
          rw [Finset.sum_add_distrib]
          simp only [add_assoc]
          rw [← Finset.sum_range_succ, ← hsum']
          congr 1

end MathlibPlus.Algebra
