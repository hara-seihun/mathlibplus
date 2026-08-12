import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Algebra

/-- Claim 4846.  The two-variable complete homogeneous polynomial is exposed
by its standard finite sum. -/
theorem completeHomogeneousDeterminant_claim4846
    {R : Type} [CommRing R] (x y : R) {a b : ℕ}
    (hb : 1 ≤ b) (hba : b ≤ a) :
    (let h : ℕ → R := fun n =>
      ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k)
     h a * h b - h (a + 1) * h (b - 1) =
       (x * y) ^ b * h (a - b)) := by
  let h : ℕ → R := fun n =>
    ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k)
  change h a * h b - h (a + 1) * h (b - 1) =
    (x * y) ^ b * h (a - b)
  have hzero : h 0 = 1 := by
    simp [h]
  have hrecX : ∀ n : ℕ, h (n + 1) = x * h n + y ^ (n + 1) := by
    intro n
    dsimp [h]
    rw [Finset.sum_range_succ']
    have hsum :
        (∑ k ∈ Finset.range (n + 1), x ^ (k + 1) * y ^ (n + 1 - (k + 1))) =
          x * ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.succ_sub_succ, pow_succ]
      ring
    rw [hsum]
    simp
  have hrecY : ∀ n : ℕ, h (n + 1) = y * h n + x ^ (n + 1) := by
    intro n
    dsimp [h]
    rw [Finset.sum_range_succ]
    have hsum :
        (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n + 1 - k)) =
          y * ∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [Nat.succ_sub hk', pow_succ]
      ring
    rw [hsum]
    simp
  have hbase : ∀ j : ℕ, 1 ≤ j →
      h j * h j - h (j + 1) * h (j - 1) = (x * y) ^ j * h 0 := by
    intro j hj
    have hjX : h j = x * h (j - 1) + y ^ j := by
      simpa [Nat.sub_add_cancel hj] using hrecX (j - 1)
    have hjY : h j = y * h (j - 1) + x ^ j := by
      simpa [Nat.sub_add_cancel hj] using hrecY (j - 1)
    calc
      h j * h j - h (j + 1) * h (j - 1) =
          h j * (h j - x * h (j - 1)) - y ^ (j + 1) * h (j - 1) := by
            rw [hrecX j]
            ring
      _ = h j * y ^ j - y ^ (j + 1) * h (j - 1) := by
            rw [hjX]
            ring
      _ = y ^ j * (h j - y * h (j - 1)) := by
            ring
      _ = (x * y) ^ j * h 0 := by
            rw [hjY, hzero, mul_pow]
            ring
  have hstep (n : ℕ) :
      h (n + 1) * h b - h (n + 2) * h (b - 1) =
        x * (h n * h b - h (n + 1) * h (b - 1)) +
          y ^ (n + 1) * x ^ b := by
    have hbY : h b - y * h (b - 1) = x ^ b := by
      have ht := hrecY (b - 1)
      rw [Nat.sub_add_cancel hb] at ht
      rw [ht]
      ring
    rw [hrecX (n + 1)]
    have hp : y ^ (n + 2) = y ^ (n + 1) * y := by
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    rw [hp]
    calc
      h (n + 1) * h b -
            (x * h (n + 1) + y ^ (n + 1) * y) * h (b - 1) =
          x * (h n * h b - h (n + 1) * h (b - 1)) +
            y ^ (n + 1) * (h b - y * h (b - 1)) := by
              rw [hrecX n]
              ring
      _ = x * (h n * h b - h (n + 1) * h (b - 1)) +
            y ^ (n + 1) * x ^ b := by rw [hbY]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hba
  clear hba
  induction d with
  | zero =>
      simpa using hbase b hb
  | succ d ih =>
      have hstep' :
          h (b + (d + 1)) * h b - h (b + (d + 1) + 1) * h (b - 1) =
            x * (h (b + d) * h b - h (b + d + 1) * h (b - 1)) +
              y ^ (b + d + 1) * x ^ b := by
        convert hstep (b + d) using 1 <;> simp only [Nat.add_assoc] <;> omega
      rw [hstep']
      rw [ih]
      have hdiff : b + (d + 1) - b = d + 1 := by omega
      have hdiff0 : b + d - b = d := by omega
      rw [hdiff, hdiff0, hrecX d]
      rw [show b + d + 1 = b + (d + 1) by omega, pow_add, mul_pow]
      ring

end MathlibPlus.Algebra
