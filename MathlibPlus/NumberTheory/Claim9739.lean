import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

/--
The Mertens-level update is supported precisely at divisors of the new index.
Here `M` is the summatory arithmetic Möbius function, and natural division is
floor division.
-/
theorem sparseDivisorSupportedLevelUpdate_claim9739
    (N d : ℕ) (hN : 0 < N) (hd : 0 < d) :
    (let M : ℕ → ℤ := fun n =>
      ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.moebius k
     let u : ℕ → ℕ → ℤ := fun N d => M (N / d)
     u N d - u (N - 1) d =
       if d ∣ N then ArithmeticFunction.moebius (N / d) else 0) := by
  dsimp
  let M : ℕ → ℤ := fun n =>
    ∑ k ∈ Finset.range (n + 1), ArithmeticFunction.moebius k
  have hM (q : ℕ) (hq : 0 < q) :
      M q = M (q - 1) + ArithmeticFunction.moebius q := by
    dsimp [M]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))]
    rw [Finset.sum_range_succ]
  by_cases hdiv : d ∣ N
  · change M (N / d) - M ((N - 1) / d) = _
    have hdle : d ≤ N := Nat.le_of_dvd hN hdiv
    have hqpos : 0 < N / d := Nat.div_pos hdle hd
    have hNeq : N = (N / d) * d := (Nat.div_mul_cancel hdiv).symm
    have hfloor : (N - 1) / d = N / d - 1 := by
      apply Nat.div_eq_of_lt_le
      · simpa only [Nat.sub_mul, one_mul, hNeq.symm]
        using Nat.sub_le_sub_left
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)) N
      · calc
          N - 1 < N := Nat.sub_lt hN Nat.zero_lt_one
          _ = (N / d) * d := hNeq
          _ = (N / d - 1 + 1) * d := by
            rw [Nat.sub_add_cancel
              (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqpos))]
    simp only [hdiv, if_true]
    rw [hfloor, hM (N / d) hqpos]
    ring
  · change M (N / d) - M ((N - 1) / d) = _
    have hfloor : (N - 1) / d = N / d := by
      apply Nat.div_eq_of_lt_le
      · have hle : (N / d) * d ≤ N :=
          (Nat.le_div_iff_mul_le hd).mp le_rfl
        have hne : (N / d) * d ≠ N := by
          intro heq
          apply hdiv
          refine (dvd_iff_exists_eq_mul_right).2 ⟨N / d, ?_⟩
          calc
            N = (N / d) * d := heq.symm
            _ = d * (N / d) := Nat.mul_comm _ _
        exact Nat.le_sub_one_of_lt (Nat.lt_of_le_of_ne hle hne)
      · have hlt : N < (N / d + 1) * d :=
          (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N / d))
        exact lt_trans (Nat.sub_lt hN Nat.zero_lt_one) hlt
    rw [hfloor]
    simp [hdiv]

end MathlibPlus.NumberTheory
