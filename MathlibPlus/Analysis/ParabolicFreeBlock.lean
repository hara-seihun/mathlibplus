import Mathlib

namespace MathlibPlus.Analysis

private theorem parabolicFreeBlock_step (x d : ℝ)
    (hn : 1 + (x + 1) * d ≠ 0) :
    2 - 1 / ((1 + (x + 1) * d) / (1 + x * d)) =
        1 + d / (1 + (x + 1) * d) ∧
      1 + d / (1 + (x + 1) * d) =
        (1 + (x + 2) * d) / (1 + (x + 1) * d) := by
  have hn' : 1 + x * d + d ≠ 0 := by
    convert hn using 1 <;> ring
  have hsecond :
      2 - 1 / ((1 + (x + 1) * d) / (1 + x * d)) =
        (1 + (x + 2) * d) / (1 + (x + 1) * d) := by
    rw [one_div_div]
    simp only [div_eq_mul_inv]
    apply sub_eq_zero.mp
    have hNeq : 1 + (x + 1) * d = 1 + x * d + d := by ring
    rw [hNeq]
    have hnum : 1 + (x + 2) * d = 1 + x * d + d * 2 := by ring
    rw [hnum]
    calc
      2 - (1 + x * d) * (1 + x * d + d)⁻¹ -
            (1 + x * d + d * 2) * (1 + x * d + d)⁻¹ =
          2 - 2 * (1 + x * d + d) *
            (1 + x * d + d)⁻¹ := by ring
      _ = 2 - 2 * 1 := by
        have hc : (1 + x * d + d) * (1 + x * d + d)⁻¹ = 1 :=
          mul_inv_cancel₀ hn'
        congr 1
        calc
          2 * (1 + x * d + d) * (1 + x * d + d)⁻¹ =
              2 * ((1 + x * d + d) * (1 + x * d + d)⁻¹) := by ring
          _ = 2 * 1 := by rw [hc]
      _ = 0 := by ring
  have hN : 1 + (x + 1) * d = 1 + x * d + d := by ring
  have hNnext : 1 + (x + 2) * d = 1 + x * d + d * 2 := by ring
  have hc : (1 + x * d + d) * (1 + x * d + d)⁻¹ = 1 :=
    mul_inv_cancel₀ hn'
  have hfrac :
      (1 + (x + 2) * d) / (1 + (x + 1) * d) =
        1 + d / (1 + (x + 1) * d) := by
    rw [hN, hNnext]
    simp only [div_eq_mul_inv]
    calc
      (1 + x * d + d * 2) * (1 + x * d + d)⁻¹ =
          (1 + x * d + d) * (1 + x * d + d)⁻¹ +
            d * (1 + x * d + d)⁻¹ := by ring
      _ = 1 + d * (1 + x * d + d)⁻¹ := by rw [hc]
  constructor
  · calc
      2 - 1 / ((1 + (x + 1) * d) / (1 + x * d)) =
          (1 + (x + 2) * d) / (1 + (x + 1) * d) := hsecond
      _ = 1 + d / (1 + (x + 1) * d) := hfrac
  · exact hfrac.symm

/-- Exact normalized iterate of the parabolic free-block recurrence.  The
nonvanishing hypothesis records the positive-pivot domain of the source's
free block. -/
theorem parabolicFreeBlock_iterate
    (u : ℕ → ℝ) (d : ℝ) (m : ℕ)
    (h0 : u 0 = 1 + d)
    (hrec : ∀ j, j < m → u (j + 1) = 2 - 1 / u j)
    (hden : ∀ j, j < m → 1 + ((j : ℝ) + 1) * d ≠ 0)
    (j : ℕ) (hj : j < m) :
    u (j + 1) = 1 + d / (1 + ((j : ℝ) + 1) * d) ∧
      u (j + 1) =
        (1 + ((j : ℝ) + 2) * d) / (1 + ((j : ℝ) + 1) * d) := by
  have hmain : ∀ j : ℕ, j < m →
      u (j + 1) = 1 + d / (1 + ((j : ℝ) + 1) * d) ∧
        u (j + 1) =
          (1 + ((j : ℝ) + 2) * d) / (1 + ((j : ℝ) + 1) * d) := by
    intro j
    induction j with
    | zero =>
        intro hj
        have hr := hrec 0 hj
        rw [h0] at hr
        have hd := hden 0 hj
        have hd' : 1 + d ≠ 0 := by
          convert hd using 1 <;> norm_num
        constructor <;> rw [hr] <;> field_simp [hd'] <;> ring
    | succ j ih =>
        intro hj
        have hjlt : j < m := Nat.lt_of_succ_lt hj
        have hp := ih hjlt
        have hr := hrec (j + 1) hj
        have hn := hden (j + 1) hj
        have hp' : u (j + 1) =
            (1 + (((j : ℝ) + 1) + 1) * d) /
              (1 + ((j : ℝ) + 1) * d) := by
          convert hp.2 using 1 <;> push_cast <;> ring
        have hleft : u (j + 1 + 1) =
            2 - 1 / ((1 + (((j : ℝ) + 1) + 1) * d) /
              (1 + ((j : ℝ) + 1) * d)) := by
          rw [hr, hp']
        have hn' : 1 + ((j : ℝ) + 1 + 1) * d ≠ 0 := by
          convert hn using 1 <;> push_cast <;> ring
        have hs := parabolicFreeBlock_step ((j : ℝ) + 1) d hn'
        have hs₁ :
            2 - 1 / ((1 + (((j : ℝ) + 1) + 1) * d) /
              (1 + ((j : ℝ) + 1) * d)) =
                1 + d / (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) := by
          convert hs.1 using 1 <;> push_cast <;> ring
        have hs₂ :
            1 + d / (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) =
              (1 + (((j + 1 : ℕ) : ℝ) + 2) * d) /
                (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) := by
          convert hs.2 using 1 <;> push_cast <;> ring
        constructor
        · calc
            u (j + 1 + 1) =
                2 - 1 / ((1 + (((j : ℝ) + 1) + 1) * d) /
                  (1 + ((j : ℝ) + 1) * d)) := hleft
            _ = 1 + d / (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) := hs₁
        · calc
            u (j + 1 + 1) =
                2 - 1 / ((1 + (((j : ℝ) + 1) + 1) * d) /
                  (1 + ((j : ℝ) + 1) * d)) := hleft
            _ = 1 + d / (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) := hs₁
            _ = (1 + (((j + 1 : ℕ) : ℝ) + 2) * d) /
                (1 + (((j + 1 : ℕ) : ℝ) + 1) * d) := hs₂
  exact hmain j hj

end MathlibPlus.Analysis
