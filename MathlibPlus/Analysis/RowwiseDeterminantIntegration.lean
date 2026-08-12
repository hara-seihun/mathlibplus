import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Analysis.RowwiseDeterminantIntegration

private theorem columnwise_determinant_integration
    {r : ℕ} (f : Fin r → Fin r → ℝ → ℝ)
    (μ : Fin r → Measure ℝ)
    [hμ : ∀ i, SigmaFinite (μ i)]
    (hf : ∀ i j, Integrable (f i j) (μ j)) :
    Matrix.det (fun i j => ∫ y, f i j y ∂(μ j)) =
      ∫ x : Fin r → ℝ,
        Matrix.det (fun i j => f i j (x j)) ∂(Measure.pi μ) := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin r),
      Integrable (fun x : Fin r → ℝ =>
        ∏ i : Fin r, f (σ i) i (x i)) (Measure.pi μ) := by
    intro σ
    exact Integrable.fintype_prod (fun i => hf (σ i) i)
  have hterm : ∀ σ : Equiv.Perm (Fin r),
      Integrable (fun x : Fin r → ℝ =>
        ((σ.sign : ℤˣ) : ℝ) *
          ∏ i : Fin r, f (σ i) i (x i)) (Measure.pi μ) := by
    intro σ
    exact (hprod σ).const_mul _
  calc
    Matrix.det (fun i j => ∫ y, f i j y ∂(μ j)) =
        ∑ σ : Equiv.Perm (Fin r),
          ((σ.sign : ℤˣ) : ℝ) *
            ∏ i : Fin r, (∫ y, f (σ i) i y ∂(μ i)) := by
      simpa using (Matrix.det_apply'
        (fun i j : Fin r => ∫ y, f i j y ∂(μ j)))
    _ = ∑ σ : Equiv.Perm (Fin r),
          ∫ x : Fin r → ℝ,
            ((σ.sign : ℤˣ) : ℝ) *
              ∏ i : Fin r, f (σ i) i (x i) ∂(Measure.pi μ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [integral_const_mul, integral_fintype_prod_eq_prod]
    _ = ∫ x : Fin r → ℝ,
          ∑ σ : Equiv.Perm (Fin r),
            ((σ.sign : ℤˣ) : ℝ) *
              ∏ i : Fin r, f (σ i) i (x i) ∂(Measure.pi μ) := by
      symm
      simpa using
        (integral_finsetSum (μ := Measure.pi μ) Finset.univ (by
          intro σ hσ
          exact hterm σ))
    _ = ∫ x : Fin r → ℝ,
          Matrix.det (fun i j => f i j (x j)) ∂(Measure.pi μ) := by
      congr 1
      funext x
      simpa using (Matrix.det_apply'
        (fun i j : Fin r => f i j (x j))).symm

theorem rowwise_determinant_integration
    {r : ℕ} (f : Fin r → Fin r → ℝ → ℝ)
    (μ : Fin r → Measure ℝ)
    [hμ : ∀ i, SigmaFinite (μ i)]
    (hf : ∀ i j, Integrable (f j i) (μ i)) :
    Matrix.det (fun i j => ∫ y, f j i y ∂(μ i)) =
      ∫ x : Fin r → ℝ,
        Matrix.det (fun i j => f j i (x i)) ∂(Measure.pi μ) := by
  calc
    Matrix.det (fun i j => ∫ y, f j i y ∂(μ i)) =
        Matrix.det (fun i j => ∫ y, f i j y ∂(μ j)) := by
          change Matrix.det (fun i j : Fin r => ∫ y, f j i y ∂(μ i)) =
            (Matrix.transpose (fun i j : Fin r => ∫ y, f j i y ∂(μ i))).det
          exact (Matrix.det_transpose _).symm
    _ = ∫ x : Fin r → ℝ,
        Matrix.det (fun i j => f i j (x j)) ∂(Measure.pi μ) := by
          apply columnwise_determinant_integration
          intro i j
          exact hf j i
    _ = ∫ x : Fin r → ℝ,
        Matrix.det (fun i j => f j i (x i)) ∂(Measure.pi μ) := by
          congr 1
          funext x
          change (Matrix.transpose (fun i j : Fin r => f j i (x i))).det =
            Matrix.det (fun i j : Fin r => f j i (x i))
          exact Matrix.det_transpose _

end MathlibPlus.Analysis.RowwiseDeterminantIntegration
