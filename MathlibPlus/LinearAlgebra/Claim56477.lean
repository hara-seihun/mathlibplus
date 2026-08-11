import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim56477

noncomputable def aggregate
    {S F : Type*} [Fintype S] [Fintype F]
    (q : S → ℚ) (Q : ℚ) (p : S → F → ℚ) : F → ℚ :=
  Q⁻¹ • ∑ e : S, q e • p e

theorem commonCoboundaryAggregate
    {S F W Z : Type*} [Fintype S] [Fintype F]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]
    (q : S → ℚ) (ell : S → W) (a : S → Z) (abar : Z)
    (p : S → F → ℚ)
    (L : (F → ℚ) →ₗ[ℚ] W) (A : (F → ℚ) →ₗ[ℚ] Z)
    (Phi Psi : W →ₗ[ℚ] Z)
    (hQ : 0 < ∑ e : S, q e)
    (hq : ∀ e, 0 < q e)
    (hp : ∀ e f, 0 ≤ p e f)
    (hLcirc : ∀ e, L (p e) = ell e)
    (hAdecomp : ∀ e, a e = abar + Phi (ell e))
    (hAexp : ∀ e, A (p e) = a e + Psi (ell e))
    (hLcancel : ∑ e : S, q e • ell e = 0) :
    let Q : ℚ := ∑ e : S, q e
    let pbar : F → ℚ := aggregate q Q p
    (∀ f, 0 ≤ pbar f) ∧
      L pbar = 0 ∧
      A pbar = abar := by
  dsimp
  let Q : ℚ := ∑ e : S, q e
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  have hQinv : 0 < Q⁻¹ := inv_pos.mpr hQ
  have hsumA : ∑ e : S, q e • a e = Q • abar := by
    simp_rw [hAdecomp, smul_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_smul]
    rw [← Finset.smul_sum]
    rw [hLcancel]
    simp [Q]
  have hnonneg : ∀ f, 0 ≤ (aggregate q Q p) f := by
    intro f
    dsimp [aggregate]
    simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
    apply mul_nonneg (le_of_lt hQinv)
    apply Finset.sum_nonneg
    intro e he
    exact mul_nonneg (le_of_lt (hq e)) (hp e f)
  have hLbar : L (aggregate q Q p) = 0 := by
    dsimp [aggregate]
    rw [map_smul, map_sum]
    simp_rw [map_smul, hLcirc]
    rw [hLcancel]
    simp
  have hAbar : A (aggregate q Q p) = abar := by
    dsimp [aggregate]
    rw [map_smul, map_sum]
    simp_rw [map_smul, hAexp, smul_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_smul]
    rw [← Finset.smul_sum, ← Finset.smul_sum]
    rw [hLcancel, hsumA]
    field_simp
  exact ⟨hnonneg, hLbar, hAbar⟩

end MathlibPlus.LinearAlgebra.Claim56477
