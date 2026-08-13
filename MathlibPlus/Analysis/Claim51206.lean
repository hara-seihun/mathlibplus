import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

/--
Claim 51206, the pointwise flip-mass inequality.  The two sign-valued rows
`s` and `t` encode the values of one Boolean atom at `x` and at the coordinate
flip of `x`, while `w` is a finite normalized law on the atoms.
-/
theorem pointwiseFlipMass_claim51206
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w s t : ι → ℝ) (alpha : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (_hunit : ∑ i, w i = 1)
    (hs : ∀ i, s i = 1 ∨ s i = -1)
    (ht : ∀ i, t i = 1 ∨ t i = -1)
    (hbary : |∑ i, w i * (s i - t i)| = 2 * alpha) :
    alpha ≤ ∑ i, w i * (if s i = t i then 0 else 1) := by
  have hdiff (i : ι) :
      |s i - t i| ≤ 2 * (if s i = t i then 0 else 1 : ℝ) := by
    rcases hs i with hsi | hsi <;> rcases ht i with hti | hti
    all_goals simp [hsi, hti]
  have hterm (i : ι) :
      |w i * (s i - t i)| ≤
        w i * (2 * (if s i = t i then 0 else 1 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left (hdiff i) (hw i)
  have habs :
      |∑ i, w i * (s i - t i)| ≤
        ∑ i, w i * (2 * (if s i = t i then 0 else 1 : ℝ)) := by
    calc
      |∑ i, w i * (s i - t i)| ≤
          ∑ i, |w i * (s i - t i)| := by
        exact Finset.abs_sum_le_sum_abs
          (fun i => w i * (s i - t i)) Finset.univ
      _ ≤ ∑ i, w i * (2 * (if s i = t i then 0 else 1 : ℝ)) := by
        exact Finset.sum_le_sum (fun i _ => hterm i)
  rw [hbary] at habs
  have hsum :
      (∑ i, w i * (2 * (if s i = t i then 0 else 1 : ℝ))) =
        2 * (∑ i, w i * (if s i = t i then 0 else 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at habs
  linarith

end MathlibPlus.Analysis
