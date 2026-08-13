import Mathlib

namespace MathlibPlus.Algebra.Claim9375

open scoped BigOperators

private lemma max_succ_right_rat (m M : ℕ) (hm : m < M) :
    (max (m + 1) (M + 1) : ℚ) = (M + 1 : ℚ) := by
  rw [max_eq_right]
  exact_mod_cast (Nat.succ_le_succ (Nat.le_of_lt hm))

private lemma max_succ_left_rat (m M : ℕ) (hm : m < M) :
    (max (M + 1) (m + 1) : ℚ) = (M + 1 : ℚ) := by
  rw [max_eq_left]
  exact_mod_cast (Nat.succ_le_succ (Nat.le_of_lt hm))

theorem finiteMaxKernelLayering_claim9375 (a : ℕ → ℚ) :
    let A : ℕ → ℚ := fun n => ∑ k ∈ Finset.range n, a (k + 1)
    ∀ M : ℕ, 0 < M →
      (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M,
          a (m + 1) * a (n + 1) / (max (m + 1) (n + 1) : ℚ)) =
        A M ^ 2 / (M : ℚ) +
          ∑ k ∈ Finset.range (M - 1),
            A (k + 1) ^ 2 / ((k + 1 : ℕ) : ℚ) / ((k + 2 : ℕ) : ℚ) := by
  dsimp only
  let A : ℕ → ℚ := fun n => ∑ k ∈ Finset.range n, a (k + 1)
  change ∀ M : ℕ, 0 < M →
      (∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M,
          a (m + 1) * a (n + 1) / (max (m + 1) (n + 1) : ℚ)) =
        A M ^ 2 / (M : ℚ) +
          ∑ k ∈ Finset.range (M - 1),
            A (k + 1) ^ 2 / ((k + 1 : ℕ) : ℚ) / ((k + 2 : ℕ) : ℚ)
  intro M
  induction M with
  | zero =>
      intro h
      omega
  | succ M ih =>
      intro hpos
      by_cases hM : M = 0
      · subst M
        simp [A]
        ring
      · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
        have hIH := ih hMpos
        simp only [Finset.sum_range_succ]
        have hcross₁ :
            (∑ x ∈ Finset.range M,
              a (x + 1) * a (M + 1) / (max (x + 1) (M + 1) : ℚ)) =
              A M * a (M + 1) / (M + 1 : ℚ) := by
          calc
            (∑ x ∈ Finset.range M,
                a (x + 1) * a (M + 1) /
                  (max (x + 1) (M + 1) : ℚ)) =
                ∑ x ∈ Finset.range M,
                  a (x + 1) * a (M + 1) / (M + 1 : ℚ) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [max_succ_right_rat x M (Finset.mem_range.mp hx)]
            _ = A M * a (M + 1) / (M + 1 : ℚ) := by
              simp only [A, div_eq_mul_inv]
              rw [Finset.sum_mul]
              rw [← Finset.sum_mul]
        have hcross₂ :
            (∑ n ∈ Finset.range M,
              a (M + 1) * a (n + 1) / (max (M + 1) (n + 1) : ℚ)) =
              a (M + 1) * A M / (M + 1 : ℚ) := by
          calc
            (∑ n ∈ Finset.range M,
                a (M + 1) * a (n + 1) /
                  (max (M + 1) (n + 1) : ℚ)) =
                ∑ n ∈ Finset.range M,
                  a (M + 1) * a (n + 1) / (M + 1 : ℚ) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [max_succ_left_rat n M (Finset.mem_range.mp hn)]
            _ = a (M + 1) * A M / (M + 1 : ℚ) := by
              simp only [A, div_eq_mul_inv]
              rw [Finset.mul_sum]
              rw [← Finset.sum_mul]
        have hdiag :
            a (M + 1) * a (M + 1) /
                (max (M + 1) (M + 1) : ℚ) =
              a (M + 1) ^ 2 / (M + 1 : ℚ) := by
          rw [max_self]
          ring
        rw [Finset.sum_add_distrib]
        rw [hcross₁, hcross₂, hdiag, hIH]
        have hrange : M + 1 - 1 = M := by omega
        have hprev : M - 1 + 1 = M := by omega
        rw [hrange]
        have hA_succ : A (M + 1) = A M + a (M + 1) := by
          change (∑ k ∈ Finset.range (M + 1), a (k + 1)) =
            (∑ k ∈ Finset.range M, a (k + 1)) + a (M + 1)
          rw [Finset.sum_range_succ]
        have hsum_succ :
            (∑ k ∈ Finset.range M,
              A (k + 1) ^ 2 / ((k + 1 : ℕ) : ℚ) /
                ((k + 2 : ℕ) : ℚ)) =
              (∑ k ∈ Finset.range (M - 1),
                A (k + 1) ^ 2 / ((k + 1 : ℕ) : ℚ) /
                  ((k + 2 : ℕ) : ℚ)) +
                A M ^ 2 / (M : ℚ) / (M + 1 : ℚ) := by
          have hsum := Finset.sum_range_succ
            (fun k => A (k + 1) ^ 2 / ((k + 1 : ℕ) : ℚ) /
              ((k + 2 : ℕ) : ℚ)) (M - 1)
          rw [hprev] at hsum
          have hidx : M - 1 + 2 = M + 1 := by omega
          rw [hidx] at hsum
          simpa [Nat.cast_add, Nat.cast_one] using hsum
        rw [hsum_succ, hA_succ]
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        ring

end MathlibPlus.Algebra.Claim9375
