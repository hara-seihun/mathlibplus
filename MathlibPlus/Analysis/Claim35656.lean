import Mathlib

namespace MathlibPlus.Analysis

open scoped BigOperators

/-- The positive dyadic weights have total mass `2`; consequently every binary
subseries has a value in the interval `[0, 2]`. -/
theorem dyadicWeightMass_claim35656 :
    (∑' j : ℕ, (j : ℝ) / (2 : ℝ) ^ j) = 2 ∧
      ∀ (ε : ℕ → Bool) (X : ℝ),
        HasSum (fun j : ℕ =>
          if ε j = true then (j : ℝ) / (2 : ℝ) ^ j else 0) X →
        0 ≤ X ∧ X ≤ 2 := by
  have hgeom :
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)) = 4 := by
    have h := tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
      (r := (1 / 2 : ℝ)) (by norm_num)
    calc
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n)) =
          1 / (1 - (1 / 2 : ℝ)) ^ (1 + 1) := by
            simpa [Nat.choose_one_right] using h
      _ = 4 := by norm_num
  have hgeom' :
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) = 4 := by
    calc
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) =
          ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) ^ n) := by
            apply tsum_congr
            intro n
            simp [one_div_pow, div_eq_mul_inv, mul_comm]
      _ = 4 := hgeom
  have hshift :
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) = 2 := by
    calc
      (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) =
          ∑' n : ℕ, (1 / 2 : ℝ) *
            (((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
              apply tsum_congr
              intro n
              rw [pow_succ]
              field_simp
      _ = (1 / 2 : ℝ) *
            (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) := by
              rw [tsum_mul_left]
      _ = 2 := by rw [hgeom']; norm_num
  have hweightSummable :
      Summable (fun j : ℕ => (j : ℝ) / (2 : ℝ) ^ j) := by
    simpa [div_eq_mul_inv, one_div_pow] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := (1 / 2 : ℝ)) (by norm_num))
  have hweightSum : (∑' j : ℕ, (j : ℝ) / (2 : ℝ) ^ j) = 2 := by
    calc
      (∑' j : ℕ, (j : ℝ) / (2 : ℝ) ^ j) =
          (∑ i ∈ Finset.range 1, (i : ℝ) / (2 : ℝ) ^ i) +
            ∑' i : ℕ, ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (i + 1) :=
        (hweightSummable.sum_add_tsum_nat_add 1).symm
      _ = ∑' i : ℕ, ((i + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (i + 1) := by
        norm_num
      _ = 2 := hshift
  refine ⟨hweightSum, ?_⟩
  intro ε X hX
  have hnonneg : ∀ j : ℕ, 0 ≤
      (if ε j = true then (j : ℝ) / (2 : ℝ) ^ j else 0) := by
    intro j
    split <;> positivity
  have hle : ∀ j : ℕ,
      (if ε j = true then (j : ℝ) / (2 : ℝ) ^ j else 0) ≤
        (j : ℝ) / (2 : ℝ) ^ j := by
    intro j
    split
    · exact le_rfl
    · positivity
  have hweightHas : HasSum (fun j : ℕ => (j : ℝ) / (2 : ℝ) ^ j) 2 := by
    simpa only [hweightSum] using hweightSummable.hasSum
  exact ⟨hX.nonneg hnonneg, hasSum_le hle hX hweightHas⟩

end MathlibPlus.Analysis
