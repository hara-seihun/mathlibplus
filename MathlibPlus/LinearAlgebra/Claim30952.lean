import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim30952

/-- If a subspace of linear functionals contains one nonzero evaluation at a
nonzero vector over `𝔽₃`, evaluation at that vector is onto.  This is the
formal algebraic consequence of the source's affine-separation statement. -/
theorem evaluation_surjective_of_separation_claim30952
    (K : Submodule (ZMod 3)
      ((Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3))
    (h : Fin 5 → ZMod 3) (_hh : h ≠ 0) (ℓ : K)
    (hℓ : (ℓ : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) h ≠ 0) :
    Function.Surjective
      ({ toFun := fun f : K =>
          (f : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) h
         map_add' := by
           intro f g
           simp
         map_smul' := by
           intro c f
           simp } : K →ₗ[ZMod 3] ZMod 3) := by
  let ev : K →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun f : K =>
        (f : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) h
      map_add' := by
        intro f g
        simp
      map_smul' := by
        intro c f
        simp }
  have hev : ev ℓ ≠ 0 := by
    simpa [ev] using hℓ
  intro z
  refine ⟨(z / ev ℓ) • ℓ, ?_⟩
  change (z / ev ℓ) * ev ℓ = z
  exact div_mul_cancel₀ z hev

/-- The separation hypothesis at every nonzero vector gives surjective
coefficient evaluation at every such vector. -/
theorem all_nonzero_evaluations_surjective_claim30952
    (K : Submodule (ZMod 3)
      ((Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3))
    (hsep : ∀ h : Fin 5 → ZMod 3, h ≠ 0 →
      ∃ ℓ : K,
        (ℓ : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) h ≠ 0) :
    ∀ h : Fin 5 → ZMod 3, h ≠ 0 →
      Function.Surjective
        ({ toFun := fun f : K =>
            (f : (Fin 5 → ZMod 3) →ₗ[ZMod 3] ZMod 3) h
           map_add' := by
             intro f g
             simp
           map_smul' := by
             intro c f
             simp } : K →ₗ[ZMod 3] ZMod 3) := by
  intro h hh
  obtain ⟨ℓ, hℓ⟩ := hsep h hh
  exact evaluation_surjective_of_separation_claim30952 K h hh ℓ hℓ

end MathlibPlus.LinearAlgebra.Claim30952
