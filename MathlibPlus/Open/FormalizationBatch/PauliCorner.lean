import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch

namespace Pauli

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

def pauliX : M2 := !![0, 1; 1, 0]
def pauliZ : M2 := !![1, 0; 0, -1]
def pauliIY : M2 := !![0, 1; -1, 0]
def leftX : M2 →ₗ[ℂ] M2 := LinearMap.mulLeft ℂ pauliX
def rightX : M2 →ₗ[ℂ] M2 := LinearMap.mulRight ℂ pauliX
def productX : M2 →ₗ[ℂ] M2 := leftX.comp rightX

def claim7016 : Prop :=
  leftX.comp rightX = rightX.comp leftX ∧
    LinearMap.ker (productX - LinearMap.id) =
      Submodule.span ℂ ({(1 : M2), pauliX} : Set M2) ∧
    LinearMap.ker (productX + LinearMap.id) =
      Submodule.span ℂ ({pauliZ, pauliIY} : Set M2)

end Pauli

end MathlibPlus.Open.FormalizationBatch
