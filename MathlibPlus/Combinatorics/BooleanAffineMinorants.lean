import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics

/-! Formalization of admitted claim 47571 (R-3667). -/

/-- The first-level absolute-coefficient bound makes every bounded sign choice
an affine minorant on the Boolean table. -/
theorem affineMinorantFromFirstLevelBound_claim47571
    {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (h : Ω → ℝ) (coordinate : ι → Ω → ℝ)
    (A : (Ω → ℝ) → ℝ)
    (_hBoolean : ∀ x, h x = 1 ∨ h x = -1)
    (_hcard : (Fintype.card Ω : ℝ) ≠ 0)
    (hbound :
      (∑ i, |(Fintype.card Ω : ℝ)⁻¹ *
        ∑ x, h x * coordinate i x|) ≤ A h)
    (ε : ι → ℝ) (hε : ∀ i, |ε i| ≤ 1) :
    ∑ i, ε i * ((Fintype.card Ω : ℝ)⁻¹ *
      ∑ x, h x * coordinate i x) ≤ A h := by
  calc
    ∑ i, ε i * ((Fintype.card Ω : ℝ)⁻¹ *
        ∑ x, h x * coordinate i x) ≤
        ∑ i, |ε i| * |(Fintype.card Ω : ℝ)⁻¹ *
          ∑ x, h x * coordinate i x| := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ε i * ((Fintype.card Ω : ℝ)⁻¹ *
            ∑ x, h x * coordinate i x) ≤
            |ε i * ((Fintype.card Ω : ℝ)⁻¹ *
              ∑ x, h x * coordinate i x)| := le_abs_self _
        _ = |ε i| * |(Fintype.card Ω : ℝ)⁻¹ *
            ∑ x, h x * coordinate i x| := by rw [abs_mul]
    _ ≤ ∑ i, |(Fintype.card Ω : ℝ)⁻¹ *
        ∑ x, h x * coordinate i x| := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        |ε i| * |(Fintype.card Ω : ℝ)⁻¹ *
            ∑ x, h x * coordinate i x| ≤
            1 * |(Fintype.card Ω : ℝ)⁻¹ *
              ∑ x, h x * coordinate i x| :=
          mul_le_mul_of_nonneg_right (hε i) (abs_nonneg _)
        _ = |(Fintype.card Ω : ℝ)⁻¹ *
            ∑ x, h x * coordinate i x| := one_mul _
    _ ≤ A h := hbound

end MathlibPlus.Combinatorics
