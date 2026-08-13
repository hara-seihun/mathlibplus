import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

open scoped BigOperators

private lemma sum_shift_id_rat (n : ℕ) :
    ∑ r ∈ Finset.range n, ((r + 1 : ℕ) : ℚ) =
      (n : ℚ) * (n + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    norm_num [Nat.cast_succ]
    ring

private lemma sum_shift_sq_rat (n : ℕ) :
    ∑ r ∈ Finset.range n, ((r + 1 : ℕ) : ℚ)^2 =
      (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    norm_num [Nat.cast_succ]
    ring

/-- Exact closed form for the coarse independent-policy active reserve in
R-4017#S2, with the displayed `r = 1, ..., n` range kept literally. -/
theorem claim49449_activeReserve (n : ℕ) (hn : 0 < n) :
    (∑ r ∈ Finset.Icc 1 n,
      (r : ℚ) / n * (1 - (r : ℚ) / n^2)) =
      (n + 1 : ℚ) * (n - 1 : ℚ) * (3 * n + 1 : ℚ) / (6 * n^2) := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext r
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hrange : n + 1 - 1 = n := by omega
  rw [hrange]
  have hterm (r : ℕ) :
      ((1 + r : ℕ) : ℚ) / n *
          (1 - ((1 + r : ℕ) : ℚ) / n^2) =
        ((1 + r : ℕ) : ℚ) / n - ((1 + r : ℕ) : ℚ)^2 / n^3 := by ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  have hid :
      (∑ r ∈ Finset.range n, ((1 + r : ℕ) : ℚ)) =
        (n : ℚ) * (n + 1) / 2 := by
    simpa [Nat.add_comm] using sum_shift_id_rat n
  have hsq :
      (∑ r ∈ Finset.range n, ((1 + r : ℕ) : ℚ)^2) =
        (n : ℚ) * (n + 1) * (2 * n + 1) / 6 := by
    simpa [Nat.add_comm] using sum_shift_sq_rat n
  rw [hid, hsq]
  field_simp
  ring

end MathlibPlus.NumberTheory
