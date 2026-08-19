import Mathlib

namespace MathlibPlus.GroupTheory

/-- The translation part of a subgroup of a semidirect product is normal. -/
theorem translationPart_normal_claim39442
    {W C : Type*} [Group W] [Group C]
    (φ : C →* MulAut W)
    (Γ : Subgroup (W ⋊[φ] C)) :
    ((SemidirectProduct.inl : W →* W ⋊[φ] C).range.subgroupOf Γ).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact Subgroup.le_normalizer_of_normal

/-- The quotient by the translation part of a subgroup of a semidirect product
embeds in the acting factor. -/
theorem quotientEmbedsInLinearImage_claim39442
    {W C : Type*} [Group W] [Group C]
    (φ : C →* MulAut W)
    (Γ : Subgroup (W ⋊[φ] C)) :
    ∃ e : (Γ ⧸ (SemidirectProduct.rightHom.comp Γ.subtype).ker) →* C,
      Function.Injective e ∧
        (SemidirectProduct.rightHom.comp Γ.subtype).ker =
          (SemidirectProduct.inl : W →* W ⋊[φ] C).range.subgroupOf Γ := by
  let f : Γ →* C :=
    SemidirectProduct.rightHom.comp Γ.subtype
  have hker : f.ker =
      (SemidirectProduct.inl : W →* W ⋊[φ] C).range.subgroupOf Γ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_subgroupOf.mpr
      rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      change SemidirectProduct.rightHom (x : W ⋊[φ] C) = 1
      exact hx
    · intro x hx
      change SemidirectProduct.rightHom (x : W ⋊[φ] C) = 1
      have hx' : (x : W ⋊[φ] C) ∈
          (SemidirectProduct.inl : W →* W ⋊[φ] C).range :=
        Subgroup.mem_subgroupOf.mp hx
      rw [SemidirectProduct.range_inl_eq_ker_rightHom] at hx'
      exact hx'
  let e0 : (Γ ⧸ f.ker) ≃* ↥f.range :=
    QuotientGroup.quotientKerEquivRange f
  let e : (Γ ⧸ f.ker) →* C :=
    (f.range.subtype).comp e0.toMonoidHom
  refine ⟨e, ?_, ?_⟩
  · intro x y hxy
    apply e0.injective
    apply Subtype.ext
    exact hxy
  · exact hker

/-- The finite quotient has order dividing the order of the linear image. -/
theorem quotientOrder_dvdLinearImage_claim39442
    {W C : Type*} [Group W] [Group C]
    [Fintype W] [Fintype C]
    (φ : C →* MulAut W)
    (Γ : Subgroup (W ⋊[φ] C)) :
    Nat.card (Γ ⧸ (SemidirectProduct.rightHom.comp Γ.subtype).ker) ∣ Nat.card C := by
  let f : Γ →* C := SemidirectProduct.rightHom.comp Γ.subtype
  let e0 : (Γ ⧸ f.ker) ≃* ↥f.range :=
    QuotientGroup.quotientKerEquivRange f
  change Nat.card (Γ ⧸ f.ker) ∣ Nat.card C
  rw [Nat.card_congr e0.toEquiv]
  exact f.range.card_subgroup_dvd_card

/-- Any natural-number prime excluded from the linear-image order is excluded
from the finite quotient order as well. -/
theorem quotientOrder_not_dvd_of_not_dvdLinearImage_claim39442
    {W C : Type*} [Group W] [Group C]
    [Fintype W] [Fintype C]
    (φ : C →* MulAut W)
    (Γ : Subgroup (W ⋊[φ] C))
    (p : ℕ)
    (hp : ¬ p ∣ Nat.card C) :
    ¬ p ∣ Nat.card (Γ ⧸ (SemidirectProduct.rightHom.comp Γ.subtype).ker) := by
  intro hq
  exact hp (hq.trans (quotientOrder_dvdLinearImage_claim39442 φ Γ))

end MathlibPlus.GroupTheory
