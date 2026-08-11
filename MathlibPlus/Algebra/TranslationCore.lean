import Mathlib

namespace MathlibPlus.Algebra.TranslationCore

/-- The translation subgroup is normal in every subgroup of a semidirect product.

The semidirect product is Mathlib's model for the affine group `W ⋊ N`; the
subgroup `range inl` is the translation subgroup, and `subgroupOf Γ` is its
intersection with `Γ`, regarded as a subgroup of `Γ`. -/
theorem translation_core_normalized
    {W N : Type*} [Group W] [Group N]
    (φ : N →* MulAut W)
    (Γ : Subgroup (W ⋊[φ] N)) :
    ((SemidirectProduct.inl : W →* W ⋊[φ] N).range.subgroupOf Γ).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  exact Subgroup.le_normalizer_of_normal

end MathlibPlus.Algebra.TranslationCore
