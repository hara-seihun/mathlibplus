import Mathlib

namespace MathlibPlus.Open.ResearchBatch.ActualAffine

noncomputable section
open Classical

abbrev F3 := ZMod 3
abbrev H3 := Fin 5 → F3
abbrev Omega3 := F3 × H3
abbrev Hdual := H3 →ₗ[F3] F3

/-- The affine-function image element from Claim 32614. -/
def affineFunctionPerm (c : F3) (ell : Hdual) (h : H3) :
    Equiv.Perm Omega3 :=
  { toFun := fun z => (z.1 + c + ell z.2, z.2 + h)
    invFun := fun z => (z.1 - c - ell (z.2 - h), z.2 - h)
    left_inv := by
      intro z
      ext <;> simp [LinearMap.map_sub] <;> ring
    right_inv := by
      intro z
      ext <;> simp [LinearMap.map_sub] <;> ring }

def affineImage : Set (Equiv.Perm Omega3) :=
  {σ | ∃ c : F3, ∃ ell : Hdual, ∃ h : H3,
    σ = affineFunctionPerm c ell h}

def translationImage : Set (Equiv.Perm Omega3) :=
  {σ | ∃ c : F3, ∃ h : H3,
    σ = affineFunctionPerm c 0 h}

def affineImageGroup : Subgroup (Equiv.Perm Omega3) :=
  Subgroup.closure affineImage

def translationImageGroup : Subgroup (Equiv.Perm Omega3) :=
  Subgroup.closure translationImage

def regularAffineSubgroup (H : Subgroup (Equiv.Perm Omega3)) : Prop :=
  ∀ x y : Omega3, ∃! h : H, h.1 x = y

def normalInAffine (H X : Subgroup (Equiv.Perm Omega3)) : Prop :=
  ∀ x : X, ∀ h : H, x.1 * h.1 * x.1⁻¹ ∈ H

/-- Claim 32614. -/
def claim_32614 : Prop :=
  affineImage =
    {σ | ∃ c : F3, ∃ ell : Hdual, ∃ h : H3,
      σ = affineFunctionPerm c ell h} ∧
    translationImage =
      {σ | ∃ c : F3, ∃ h : H3,
        σ = affineFunctionPerm c 0 h} ∧
    regularAffineSubgroup translationImageGroup ∧
    Nonempty (translationImageGroup ≃ Fin (3 ^ 6))

/-- Claim 32615. -/
def claim_32615 : Prop :=
  normalInAffine translationImageGroup affineImageGroup

end
end MathlibPlus.Open.ResearchBatch.ActualAffine
