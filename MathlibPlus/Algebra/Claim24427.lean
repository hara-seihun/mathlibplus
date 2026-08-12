import Mathlib

namespace MathlibPlus.Algebra.Claim24427

/-- The rational-coefficient relation lemma from the crossed-state affine-product
calculation.  The source's coefficient domain is made explicit as `ℚ` and its
ambient domain as `ℝ`; no assertion about the omitted product-profile objects is
made here. -/
theorem nonproportional_source_differences
    {U V : ℝ} {β γ δ : ℚ}
    (hU : U ≠ 0) (hV : V ≠ 0)
    (hnot : ¬ ∃ q : ℚ, U = (q : ℝ) * V)
    (hlin : (β : ℝ) * U + (γ : ℝ) * V = 0)
    (hprod : (δ : ℝ) * U * V = 0) :
    β = 0 ∧ γ = 0 ∧ δ = 0 := by
  have hβ : β = 0 := by
    by_contra hβ
    have hβR : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
    have hUeq : U = -((γ : ℝ) / (β : ℝ)) * V := by
      field_simp [hβR]
      nlinarith [hlin]
    apply hnot
    refine ⟨-γ / β, ?_⟩
    norm_num [div_eq_mul_inv] at hUeq ⊢
    exact hUeq
  have hγ : γ = 0 := by
    by_contra hγ
    have hlin' : (γ : ℝ) * V = 0 := by
      simpa [hβ] using hlin
    have hγR : (γ : ℝ) = 0 :=
      (mul_eq_zero.mp hlin').resolve_right hV
    exact hγ (by exact_mod_cast hγR)
  have hδ : δ = 0 := by
    have hδR : (δ : ℝ) = 0 := by
      rcases mul_eq_zero.mp hprod with hδU | hVzero
      · rcases mul_eq_zero.mp hδU with hδzero | hUzero
        · exact hδzero
        · exact False.elim (hU hUzero)
      · exact False.elim (hV hVzero)
    exact_mod_cast hδR
  exact ⟨hβ, hγ, hδ⟩

end MathlibPlus.Algebra.Claim24427
