import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The alternating-pivot sign calculation extracted from claim 17559.
The source matrix's diagonal sequence is supplied as `D`; the theorem records
its displayed closed form, nonvanishing, and sign. -/
theorem alternatingDiagonalPivots
    (D : ℕ → ℚ)
    (hD0 : D 0 = 1)
    (hD : ∀ j : ℕ, 0 < j →
      D j = ((-1 : ℚ) ^ j) /
        ((Nat.factorial (2 * j) : ℚ) * Nat.choose (2 * j - 1) (j - 1))) :
    D 0 = 1 ∧
      ∀ j : ℕ, 0 < j →
        D j = ((-1 : ℚ) ^ j) /
            ((Nat.factorial (2 * j) : ℚ) * Nat.choose (2 * j - 1) (j - 1)) ∧
        D j ≠ 0 ∧
        0 < ((-1 : ℚ) ^ j) * D j := by
  refine ⟨hD0, ?_⟩
  intro j hj
  have hjle : j - 1 ≤ 2 * j - 1 := by omega
  have hchoose : 0 < Nat.choose (2 * j - 1) (j - 1) :=
    Nat.choose_pos (by omega)
  have hfac : 0 < Nat.factorial (2 * j) := Nat.factorial_pos _
  have hden : 0 < (Nat.factorial (2 * j) : ℚ) * Nat.choose (2 * j - 1) (j - 1) := by
    positivity
  have hden0 : (Nat.factorial (2 * j) : ℚ) * Nat.choose (2 * j - 1) (j - 1) ≠ 0 :=
    ne_of_gt hden
  have hform := hD j hj
  refine ⟨hform, ?_, ?_⟩
  · rw [hform]
    exact div_ne_zero (pow_ne_zero _ (by norm_num)) hden0
  · rw [hform]
    field_simp
    simp only [zero_mul]
    apply sq_pos_of_ne_zero
    exact pow_ne_zero j (by norm_num)

end MathlibPlus.Algebra
