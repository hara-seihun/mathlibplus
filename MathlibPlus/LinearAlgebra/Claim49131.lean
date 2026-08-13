import Mathlib
open scoped BigOperators
namespace MathlibPlus.LinearAlgebra.Claim49131

/-- Claim 49131: a zero-sum quadratic form for the squared-distance matrix is
nonpositive, with the exact Gram expansion retained. -/
theorem distanceMatrix_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : Fin 9 → E) (z : Fin 9 → ℝ)
    (hz : ∑ i, z i = 0) :
    let L : Matrix (Fin 9) (Fin 9) ℝ := fun i j => ‖p i - p j‖ ^ 2
    (dotProduct z (L.mulVec z) =
      -2 * ‖∑ i, (z i) • p i‖ ^ 2) ∧
    dotProduct z (L.mulVec z) ≤ 0 := by
  dsimp
  have heq : dotProduct z (Matrix.mulVec ((fun i j => (‖p i - p j‖ ^ 2 : ℝ)) : Matrix (Fin 9) (Fin 9) ℝ) z) =
      -2 * ‖∑ i, (z i) • p i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [Matrix.mulVec, dotProduct]
    have hdist (i j : Fin 9) :
        ‖p i - p j‖ ^ 2 =
          inner ℝ (p i) (p i) - inner ℝ (p i) (p j) -
            inner ℝ (p j) (p i) + inner ℝ (p j) (p j) := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      ring
    simp_rw [hdist]
    have hleft (f : Fin 9 → E) (y : E) :
        inner ℝ (∑ i, f i) y = ∑ i, inner ℝ (f i) y := by
      classical
      induction (Finset.univ : Finset (Fin 9)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih, inner_add_left]
    have hright (x : E) (f : Fin 9 → E) :
        inner ℝ x (∑ i, f i) = ∑ i, inner ℝ x (f i) := by
      classical
      induction (Finset.univ : Finset (Fin 9)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih => simp [ha, ih, inner_add_right]
    rw [hleft]
    simp_rw [hright]
    simp_rw [real_inner_smul_left, real_inner_smul_right]
    simp_rw [sub_eq_add_neg, add_mul]
    simp only [Finset.sum_add_distrib]
    simp_rw [mul_add]
    simp only [Finset.sum_add_distrib]
    have hzero (f : Fin 9 → ℝ) :
        ∑ x, z x * ∑ y, f x * z y = 0 := by
      simp_rw [← Finset.mul_sum]
      simp [hz]
    have hzero2 (f : Fin 9 → ℝ) :
        ∑ x, z x * ∑ y, f y * z y = 0 := by
      rw [← Finset.sum_mul]
      simp [hz]
    rw [hzero, hzero2]
    simp_rw [Finset.mul_sum]
    simp_rw [real_inner_comm]
    have hcross :
        (∑ x, ∑ i, z x * (-inner ℝ (p x) (p i) * z i)) +
            (∑ x, ∑ i, z x * (-inner ℝ (p x) (p i) * z i)) =
          ∑ x, ∑ i, (-2) * (z x * (z i * inner ℝ (p x) (p i))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    simpa only [zero_add, add_zero] using hcross
  
  constructor
  · exact heq
  · rw [heq]
    nlinarith [sq_nonneg (‖∑ i, (z i) • p i‖ : ℝ)]
end MathlibPlus.LinearAlgebra.Claim49131
