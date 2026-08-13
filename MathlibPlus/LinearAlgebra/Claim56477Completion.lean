import MathlibPlus.LinearAlgebra.Claim56477

namespace MathlibPlus.LinearAlgebra.Claim56477

theorem commonCoboundaryAggregate_nonzero
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
    (hLcancel : ∑ e : S, q e • ell e = 0)
    (habar : abar ≠ 0) :
    let Q : ℚ := ∑ e : S, q e
    let pbar : F → ℚ := aggregate q Q p
    (∀ f, 0 ≤ pbar f) ∧
      L pbar = 0 ∧
      A pbar = abar ∧
      A pbar ≠ 0 := by
  have h := commonCoboundaryAggregate q ell a abar p L A Phi Psi
    hQ hq hp hLcirc hAdecomp hAexp hLcancel
  dsimp at h ⊢
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  rw [h.2.2]
  exact habar

end MathlibPlus.LinearAlgebra.Claim56477
