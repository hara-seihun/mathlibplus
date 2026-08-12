import Mathlib

namespace MathlibPlus.GroupTheory.Claim35707

/-- A characteristic subgroup is carried to the corresponding subgroup
under any isomorphism between two copies of the ambient finite group. -/
theorem conjugation_maps_characteristic_copy
    {H R T : Type*} [Group H] [Group R] [Group T]
    [Fintype H] [Fintype R] [Fintype T]
    (K : Subgroup H) [K.Characteristic]
    (eR : H ≃* R) (eT : H ≃* T) (f : R ≃* T) :
    (K.map eR.toMonoidHom).map f.toMonoidHom =
      K.map eT.toMonoidHom := by
  let φ : H ≃* H := (eR.trans f).trans eT.symm
  have hφ : K.map φ.toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ
  have hφinv : K.map φ.symm.toMonoidHom = K :=
    (Subgroup.characteristic_iff_map_eq.mp inferInstance) φ.symm
  ext y
  constructor
  · rintro ⟨x, ⟨h, hh, rfl⟩, rfl⟩
    have hφh : φ h ∈ K := by
      rw [← hφ]
      exact ⟨h, hh, rfl⟩
    exact ⟨φ h, hφh, by simp [φ]⟩
  · rintro ⟨h, hh, rfl⟩
    have hinv : φ.symm h ∈ K := by
      rw [← hφinv]
      exact ⟨h, hh, rfl⟩
    exact ⟨eR (φ.symm h), ⟨φ.symm h, hinv, rfl⟩, by simp [φ]⟩

end MathlibPlus.GroupTheory.Claim35707
