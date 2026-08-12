import Mathlib

namespace MathlibPlus.Combinatorics.Claim44178

open scoped BigOperators

/-- A monomial activation has `n - 1` distinct earlier cross-term coefficients. -/
theorem earlier_cross_term_count (n : ℕ) (hn : 1 ≤ n) :
    let coeffs : ℕ → Finset ℕ := fun n =>
      (Finset.Icc 1 (n - 1)).map
        ⟨fun j => n + j, fun _a _b h => Nat.add_left_cancel h⟩
    (coeffs n).card = n - 1 := by
  dsimp
  classical
  simp [Nat.card_Icc, hn]

/-- The complete quadratic layers at births `1` through `M` use the triangular count. -/
theorem complete_quadratic_layer_slot_count (M : ℕ) :
    let coeffs : ℕ → Finset ℕ := fun n =>
      (Finset.Icc 1 (n - 1)).map
        ⟨fun j => n + j, fun _a _b h => Nat.add_left_cancel h⟩
    (∑ n ∈ Finset.Icc 1 M, ((coeffs n).card : ℚ)) =
      (M : ℚ) * (M - 1) / 2 := by
  dsimp
  classical
  have hcounts : ∀ n ∈ Finset.Icc 1 M,
      ((Finset.Icc 1 (n - 1)).map
        ⟨fun j => n + j, fun _a _b h => Nat.add_left_cancel h⟩).card = n - 1 := by
    intro n hn
    exact earlier_cross_term_count n (Finset.mem_Icc.mp hn).1
  calc
    (∑ n ∈ Finset.Icc 1 M,
        (((Finset.Icc 1 (n - 1)).map
          ⟨fun j => n + j, fun _a _b h => Nat.add_left_cancel h⟩).card : ℚ)) =
        ∑ n ∈ Finset.Icc 1 M, ((n - 1 : ℕ) : ℚ) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hcounts n hn]
    _ = (M : ℚ) * (M - 1) / 2 := by
      -- The remaining identity is the elementary sum of `n - 1` for `1 ≤ n ≤ M`.
      clear hcounts
      induction M with
      | zero => simp
      | succ M ih =>
          rw [Finset.sum_Icc_succ_top]
          · simp only [Nat.cast_sub (show 1 ≤ M + 1 by omega)]
            rw [ih]
            push_cast
            ring
          · omega

end MathlibPlus.Combinatorics.Claim44178
