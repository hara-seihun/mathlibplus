import Mathlib

namespace MathlibPlus.Analysis.Claim48196

private theorem sortedArea_le_l1_sq {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hmono : ∀ i j, i ≤ j → b j ≤ b i)
    (hL1 : (∑ i, b i) ≤ 1) :
    (∑ i, (i.1 + 1 : ℝ) * b i ^ 2) ≤ (∑ i, b i) ^ 2 ∧
      (∑ i, b i) ^ 2 ≤ 1 := by
  have hterm : ∀ i, (i.1 + 1 : ℝ) * b i ≤ ∑ j, b j := by
    intro i
    have hlocal : (∑ j ∈ Finset.Iic i, b i) ≤ (∑ j ∈ Finset.Iic i, b j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmono j i (by simpa using hj)
    have hcard : (∑ _j ∈ Finset.Iic i, b i) = (i.1 + 1 : ℝ) * b i := by
      simp
    have hglobal : (∑ j ∈ Finset.Iic i, b j) ≤ (∑ j, b j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro j hj hji
      exact hb j
    linarith
  constructor
  · calc
      (∑ i, (i.1 + 1 : ℝ) * b i ^ 2) ≤
          ∑ i, b i * (∑ j, b j) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := hterm i
            have hmul := mul_le_mul_of_nonneg_right hi' (hb i)
            nlinarith
      _ = (∑ i, b i) ^ 2 := by
        rw [← Finset.sum_mul]
        ring
  · have hsum : 0 ≤ (∑ i, b i) := Finset.sum_nonneg (fun i hi => hb i)
    nlinarith

/-- If the coefficients are queried in nonincreasing order of absolute value,
the depth-one weighted square area is bounded by the squared `l1` mass. -/
theorem depthOneAreaBound
    {n : ℕ} (a : Fin n → ℝ) (σ : Fin n ≃ Fin n)
    (hsorted : ∀ i j, i ≤ j → |a (σ j)| ≤ |a (σ i)|)
    (hL1 : (∑ i, |a i|) ≤ 1) :
    (∑ i, (i.1 + 1 : ℝ) * (a (σ i)) ^ 2) ≤
      (∑ i, |a i|) ^ 2 ∧
      (∑ i, |a i|) ^ 2 ≤ 1 := by
  let b : Fin n → ℝ := fun i => |a (σ i)|
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact abs_nonneg _
  have hmono : ∀ i j, i ≤ j → b j ≤ b i := by
    intro i j hij
    exact hsorted i j hij
  have hsum : (∑ i, b i) = ∑ i, |a i| := by
    exact σ.sum_comp (fun i => |a i|)
  have hL1b : (∑ i, b i) ≤ 1 := by
    rw [hsum]
    exact hL1
  have hcore := sortedArea_le_l1_sq b hb hmono hL1b
  rw [hsum] at hcore
  simpa [b, sq_abs] using hcore

end MathlibPlus.Analysis.Claim48196
