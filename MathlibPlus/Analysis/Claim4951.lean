import Mathlib

namespace MathlibPlus.Analysis.Claim4951

/-- A strictly positive finite quadrature on each cell preserves strict positivity
of that cell's evaluation.  The normalization of a quadrature is immaterial to
this positivity conclusion, so it is not added as an unstated hypothesis. -/
theorem positive_cell_quadrature_preserves_strict
    {n m : ℕ} (w f : Fin n → Fin m → ℝ) (hm : 0 < m)
    (hw : ∀ i j, 0 < w i j) (hf : ∀ i j, 0 < f i j) :
    ∀ i, 0 < ∑ j, w i j * f i j := by
  intro i
  apply Finset.sum_pos
  · intro j hj
    exact mul_pos (hw i j) (hf i j)
  · let j₀ : Fin m := ⟨0, hm⟩
    exact ⟨j₀, Finset.mem_univ j₀⟩

end MathlibPlus.Analysis.Claim4951
