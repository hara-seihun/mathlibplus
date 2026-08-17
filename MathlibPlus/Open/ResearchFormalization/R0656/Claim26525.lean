import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0656

abbrev A2 := Fin 2 → ℚ
abbrev A3 := Fin 4 → ℚ

/-- The ordered bases of the two exact reduced scalar spaces. -/
def a2_s_squared : A2 := fun i => if i = 0 then 1 else 0
def a2_q : A2 := fun i => if i = 1 then 1 else 0

def a3_s_cubed : A3 := fun i => if i = 0 then 1 else 0
def a3_s_q : A3 := fun i => if i = 1 then 1 else 0
def a3_p_sub_c : A3 := fun i => if i = 2 then 1 else 0
def a3_c_sub_se : A3 := fun i => if i = 3 then 1 else 0

def a3DefectSpan : Submodule ℚ A3 :=
  Submodule.span ℚ
    ({a3_s_q, a3_p_sub_c, a3_c_sub_se} : Set A3)

abbrev MixedCorrectionSpace :=
  TensorProduct ℚ A2 A3 × TensorProduct ℚ A3 A2

def mixedCorrectionSubspace :
    Submodule ℚ MixedCorrectionSpace :=
  ⊤

def pureSymmetricTensor (r : A3) : MixedCorrectionSpace :=
  (TensorProduct.tmul ℚ a2_q r,
    TensorProduct.tmul ℚ r a2_q)

def pureSymmetricQSubspace :
    Submodule ℚ MixedCorrectionSpace :=
  Submodule.span ℚ
    {x | ∃ r : A3, r ∈ a3DefectSpan ∧ x = pureSymmetricTensor r}

abbrev MixedParameterCarrier := Fin 16 → ℚ

/-- The complete nonsymmetric mixed correction carrier is the direct sum of
 the exact 2|3 and 3|2 tensor spaces.  The symmetric q⊗r+r⊗q ansatz is an
 explicit proper subspace, not an unrelated coordinate count. -/
def completeMixedReducedCorrectionSpace_claim26525 : Prop :=
  Nonempty (MixedCorrectionSpace ≃ₗ[ℚ] MixedParameterCarrier) ∧
    Module.finrank ℚ MixedCorrectionSpace = 16 ∧
      pureSymmetricQSubspace ≤ mixedCorrectionSubspace ∧
        pureSymmetricQSubspace ≠ mixedCorrectionSubspace

end MathlibPlus.Open.ResearchFormalization.R0656
