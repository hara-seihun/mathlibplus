import Mathlib

namespace MathlibPlus.Combinatorics

private lemma negOne_pow_shift (i j : ℕ) (hij : i < j) :
    (-1 : ℤ) ^ (j - i - 1) = (-1 : ℤ) ^ (i + 1) * (-1 : ℤ) ^ j := by
  let a : ℤ := (-1 : ℤ) ^ (j - i - 1)
  let b : ℤ := (-1 : ℤ) ^ (i + 1)
  let c : ℤ := (-1 : ℤ) ^ j
  have hsum : j - i - 1 + (i + 1) = j := by omega
  have hab : a * b = c := by
    dsimp [a, b, c]
    rw [← pow_add, hsum]
  have hb : b * b = 1 := by
    dsimp [b]
    rw [← pow_add]
    rw [show (i + 1) + (i + 1) = 2 * (i + 1) by omega, pow_mul]
    norm_num
  dsimp [a, b, c] at hab hb ⊢
  calc
    a = a * (b * b) := by rw [hb, mul_one]
    _ = (a * b) * b := by ring
    _ = c * b := by rw [hab]
    _ = b * c := by ring

/-- Claim 19651: the alternating binomial tail propagates the coefficient
at the preceding level. -/
theorem alternatingBinomialPropagation_claim19651 (n i : ℕ) (hi : i < n) :
    Finset.sum ((Finset.range (n + 1)).filter (fun j => i < j))
        (fun j => (-1 : ℤ) ^ (j - i - 1) * (Nat.choose n j : ℤ)) =
      (Nat.choose (n - 1) i : ℤ) := by
  let f : ℕ → ℤ := fun j => (-1 : ℤ) ^ j * (Nat.choose n j : ℤ)
  have hn : 1 ≤ n := by omega
  have hprefix :
      (∑ j ∈ Finset.range (i + 1), f j) =
        (-1 : ℤ) ^ i * (Nat.choose (n - 1) i : ℤ) := by
    dsimp [f]
    simpa [Nat.sub_add_cancel hn] using
      (Int.alternating_sum_range_choose_eq_choose (n := n - 1) (m := i))
  have htotal : (∑ j ∈ Finset.range (n + 1), f j) = 0 := by
    dsimp [f]
    simpa using (Int.alternating_sum_range_choose_of_ne (n := n) (by omega))
  have hnot :
      (Finset.range (n + 1)).filter (fun j => ¬ i < j) = Finset.range (i + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, not_lt]
    omega
  have htailbase :
      Finset.sum ((Finset.range (n + 1)).filter (fun j => i < j)) f =
        -((-1 : ℤ) ^ i * (Nat.choose (n - 1) i : ℤ)) := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
        (fun j => i < j) f
    rw [hnot, hprefix, htotal] at hsplit
    linarith
  calc
    Finset.sum ((Finset.range (n + 1)).filter (fun j => i < j))
        (fun j => (-1 : ℤ) ^ (j - i - 1) * (Nat.choose n j : ℤ)) =
        Finset.sum ((Finset.range (n + 1)).filter (fun j => i < j))
          (fun j => (-1 : ℤ) ^ (i + 1) * f j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hij : i < j := by
              simpa using (Finset.mem_filter.mp hj).2
            rw [negOne_pow_shift i j hij]
            simp [f]
            ring
    _ = (-1 : ℤ) ^ (i + 1) *
        Finset.sum ((Finset.range (n + 1)).filter (fun j => i < j)) f := by
          rw [Finset.mul_sum]
    _ = (Nat.choose (n - 1) i : ℤ) := by
      rw [htailbase]
      have hsign : (-1 : ℤ) ^ i * (-1 : ℤ) ^ i = 1 := by
        rw [← pow_add]
        rw [show i + i = 2 * i by omega, pow_mul]
        norm_num
      rw [pow_succ]
      calc
        (-1 : ℤ) ^ i * (-1) *
              -((-1 : ℤ) ^ i * (Nat.choose (n - 1) i : ℤ)) =
            ((-1 : ℤ) ^ i * (-1 : ℤ) ^ i) *
              (Nat.choose (n - 1) i : ℤ) := by ring
        _ = (Nat.choose (n - 1) i : ℤ) := by rw [hsign]; ring

end MathlibPlus.Combinatorics
