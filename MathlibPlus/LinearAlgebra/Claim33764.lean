import MathlibPlus.Basic

open Finset

namespace MathlibPlus.LinearAlgebra.Claim33764

/--
Formalization of admitted claim 33764.  The dual certificate is written over
`ℚ`, so the multipliers are literally rational.  The source's x₁-free
condition is retained as `v ⟨0, hn⟩ = 0`; it is not needed by weak duality
itself, but is part of the stated data.
-/
theorem atomMultiplicityDualLowerBound
    {n m : ℕ} (hn : 0 < n) (a b w : Fin n → ℚ)
    (rows : Fin m → Fin n → ℚ)
    (v : Fin n → ℚ) (_hv_free : v ⟨0, hn⟩ = 0)
    (σ : ℚ) (y : Fin m → ℚ) (yLam : ℚ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hrows : ∀ r, dotProduct (rows r) (a - b) = 0)
    (hv : dotProduct v (a - b) = σ)
    (hdual_nonneg : ∀ i,
      0 ≤ (∑ r, y r * rows r i) + yLam * v i)
    (hdual_le : ∀ i,
      (∑ r, y r * rows r i) + yLam * v i ≤ w i) :
    σ * yLam ≤ dotProduct w a := by
  let g : Fin n → ℚ := fun i => (∑ r, y r * rows r i) + yLam * v i
  have hga : dotProduct g a ≤ dotProduct w a := by
    unfold dotProduct
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hdual_le i) (ha i)
  have hgb : 0 ≤ dotProduct g b := by
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hdual_nonneg i) (hb i)
  have hrows' : ∀ r, (∑ i, rows r i * (a i - b i)) = 0 := by
    intro r
    simpa [dotProduct, sub_apply] using hrows r
  have hv' : (∑ i, v i * (a i - b i)) = σ := by
    simpa [dotProduct, sub_apply] using hv
  have hgdiff : dotProduct g (a - b) = σ * yLam := by
    unfold dotProduct g
    calc
      (∑ i, ((∑ r, y r * rows r i) + yLam * v i) * (a i - b i)) =
          (∑ r, y r * (∑ i, rows r i * (a i - b i))) +
            yLam * (∑ i, v i * (a i - b i)) := by
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib]
              congr 1
              · simp_rw [Finset.sum_mul]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro r hr
                calc
                  (∑ i, (y r * rows r i) * (a i - b i)) =
                      ∑ i, y r * (rows r i * (a i - b i)) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                  _ = y r * (∑ i, rows r i * (a i - b i)) := by
                    rw [Finset.mul_sum]
              · calc
                  (∑ i, yLam * v i * (a i - b i)) =
                      ∑ i, yLam * (v i * (a i - b i)) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                  _ = yLam * (∑ i, v i * (a i - b i)) := by
                    rw [Finset.mul_sum]
      _ = σ * yLam := by
        rw [show (∑ r, y r * (∑ i, rows r i * (a i - b i))) = 0 by
          apply Finset.sum_eq_zero
          intro r hr
          rw [hrows' r]
          simp]
        rw [hv']
        ring
  have hdecomp : dotProduct g (a - b) = dotProduct g a - dotProduct g b := by
    unfold dotProduct
    calc
      (∑ i, g i * (a i - b i)) = ∑ i, (g i * a i - g i * b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, g i * a i) - ∑ i, g i * b i := by
        rw [Finset.sum_sub_distrib]
  linarith [hga, hgb, hgdiff, hdecomp]

end MathlibPlus.LinearAlgebra.Claim33764
