import Mathlib

namespace MathlibPlus.Algebra

/--
A primitive integral coefficient vector cannot be scaled by a nonunit rational
while both the scaled vector and its reciprocal scaling remain integral.
-/
theorem primitive_reciprocal_integrality_claim28158
    {n : ℕ} (D : Fin n → ℤ)
    (hD : Finset.univ.gcd D = 1)
    (c : ℚ) (hc : c ≠ 0)
    (hleft : ∃ E : Fin n → ℤ, ∀ i, (E i : ℚ) = c * (D i : ℚ))
    (hright : ∃ E : Fin n → ℤ, ∀ i, (E i : ℚ) = c⁻¹ * (D i : ℚ)) :
    (∃ z : ℤ, (z : ℚ) = c) ∧
      (∃ z : ℤ, (z : ℚ) = c⁻¹) ∧
      (c = 1 ∨ c = -1) := by
  obtain ⟨u, hu⟩ := Finset.gcd_eq_sum_mul (Finset.univ : Finset (Fin n)) D
  have hbez : (1 : ℤ) = ∑ i : Fin n, D i * u i := by
    simpa [hD] using hu
  have hbezQ : (1 : ℚ) = ∑ i : Fin n, (D i : ℚ) * (u i : ℚ) := by
    exact_mod_cast hbez
  obtain ⟨E, hE⟩ := hleft
  have hc_int : ∃ z : ℤ, (z : ℚ) = c := by
    refine ⟨∑ i : Fin n, E i * u i, ?_⟩
    calc
      (↑(∑ i : Fin n, E i * u i) : ℚ) =
          ∑ i : Fin n, (E i : ℚ) * (u i : ℚ) := by norm_num
      _ = ∑ i : Fin n, (c * (D i : ℚ)) * (u i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hE i]
      _ = c * ∑ i : Fin n, (D i : ℚ) * (u i : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c := by rw [← hbezQ, mul_one]
  obtain ⟨E₂, hE₂⟩ := hright
  have hc_inv_int : ∃ z : ℤ, (z : ℚ) = c⁻¹ := by
    refine ⟨∑ i : Fin n, E₂ i * u i, ?_⟩
    calc
      (↑(∑ i : Fin n, E₂ i * u i) : ℚ) =
          ∑ i : Fin n, (E₂ i : ℚ) * (u i : ℚ) := by norm_num
      _ = ∑ i : Fin n, (c⁻¹ * (D i : ℚ)) * (u i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hE₂ i]
      _ = c⁻¹ * ∑ i : Fin n, (D i : ℚ) * (u i : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = c⁻¹ := by rw [← hbezQ, mul_one]
  refine ⟨hc_int, hc_inv_int, ?_⟩
  obtain ⟨z, hz⟩ := hc_int
  obtain ⟨w, hw⟩ := hc_inv_int
  have hzwQ : ((z * w : ℤ) : ℚ) = 1 := by
    rw [Int.cast_mul, hz, hw]
    exact mul_inv_cancel₀ hc
  have hzw : z * w = 1 := by exact_mod_cast hzwQ
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hzw with hz1 | hzneg
  · left
    calc
      c = (z : ℚ) := hz.symm
      _ = 1 := by simp [hz1]
  · right
    calc
      c = (z : ℚ) := hz.symm
      _ = -1 := by simp [hzneg]

end MathlibPlus.Algebra
