import Mathlib

namespace MathlibPlus.Analysis

/-- Explicit form of the alternating-orientation hypothesis used in the
coefficient `l1` evaluation.  The polynomial value at `-1` is expanded as
its coefficient sum. -/
theorem alternating_coeff_l1_eq_eval_neg_one_claim7368
    (n : ℕ) (q : Fin (n + 1) → ℝ)
    (horient : ∀ j : Fin (n + 1),
      0 ≤ (-1 : ℝ) ^ (n - (j : ℕ)) * q j) :
    ∑ j : Fin (n + 1), |q j| =
      (-1 : ℝ) ^ n * ∑ j : Fin (n + 1), q j * (-1 : ℝ) ^ (j : ℕ) := by
  have hneg : ∀ k : ℕ, (-1 : ℝ) ^ k = 1 ∨ (-1 : ℝ) ^ k = -1 := by
    intro k
    induction k with
    | zero => left; simp
    | succ k ih =>
        rcases ih with hk | hk
        · right
          rw [pow_succ, hk]
          norm_num
        · left
          rw [pow_succ, hk]
          norm_num
  have hterm : ∀ j : Fin (n + 1),
      |q j| = (-1 : ℝ) ^ (n + (j : ℕ)) * q j := by
    intro j
    have hj : (j : ℕ) ≤ n := by omega
    have hpow : (-1 : ℝ) ^ (n - (j : ℕ)) =
        (-1 : ℝ) ^ (n + (j : ℕ)) := by
      calc
        (-1 : ℝ) ^ (n - (j : ℕ)) =
            (-1 : ℝ) ^ (n - (j : ℕ)) * (-1 : ℝ) ^ (2 * (j : ℕ)) := by
              have htwo : (-1 : ℝ) ^ (2 * (j : ℕ)) = 1 := by
                rw [pow_mul]
                norm_num
              rw [htwo, mul_one]
        _ = (-1 : ℝ) ^ ((n - (j : ℕ)) + 2 * (j : ℕ)) := by
              rw [pow_add]
        _ = (-1 : ℝ) ^ (n + (j : ℕ)) := by
              congr 1
              omega
    have hsign := horient j
    have hbase : |q j| = (-1 : ℝ) ^ (n - (j : ℕ)) * q j := by
      rcases hneg (n - (j : ℕ)) with hp | hm
      · have hq : 0 ≤ q j := by simpa [hp] using hsign
        simpa [hp, abs_of_nonneg hq]
      · have hqneg : q j ≤ 0 := by
          have hnonneg : 0 ≤ -q j := by simpa [hm] using hsign
          linarith
        rw [abs_of_nonpos hqneg, hm]
        ring
    rw [hpow] at hbase
    exact hbase
  calc
    ∑ j : Fin (n + 1), |q j| =
        ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (n + (j : ℕ)) * q j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm j
    _ = ∑ j : Fin (n + 1),
          ((-1 : ℝ) ^ n * (q j * (-1 : ℝ) ^ (j : ℕ))) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_add]
          ring
    _ = (-1 : ℝ) ^ n * ∑ j : Fin (n + 1), q j * (-1 : ℝ) ^ (j : ℕ) := by
          rw [Finset.mul_sum]

end MathlibPlus.Analysis
