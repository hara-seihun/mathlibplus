import MathlibPlus.Algebra.PositiveIntegralEdgeTensorClaim5278Theorems

namespace MathlibPlus.Open.Algebra

open MathlibPlus.Algebra
open scoped BigOperators TensorProduct

/-- The successor of a positive integral edge length. -/
def edgeLengthSuccessor (ℓ : PositiveEdgeLength) : PositiveEdgeLength :=
  ⟨Nat.succ ℓ.1, Nat.succ_pos ℓ.1⟩

/-- The unit positive integral edge length. -/
def unitEdgeLength : PositiveEdgeLength :=
  ⟨1, by decide⟩

/-- Unit lengthening on the free rational edge-length space. -/
noncomputable def unitLengthening :
    PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthSpace :=
  Finsupp.lmapDomain ℚ ℚ edgeLengthSuccessor

/-- Reduced deconcatenation on a positive edge basis vector. -/
noncomputable def reducedDeconcatenationOnBasis
    (ℓ : PositiveEdgeLength) :
    PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace :=
  Finset.sum (Finset.Ico 1 ℓ.1).attach (fun i =>
    positiveEdgeVector
        ⟨i.1,
          Nat.lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Ico.mp i.2).1⟩ ⊗ₜ[ℚ]
      positiveEdgeVector
        ⟨ℓ.1 - i.1, Nat.sub_pos_of_lt (Finset.mem_Ico.mp i.2).2⟩)

/-- Reduced deconcatenation extended linearly. -/
noncomputable def reducedDeconcatenation :
    PositiveEdgeLengthSpace →ₗ[ℚ]
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  Finsupp.linearCombination ℚ reducedDeconcatenationOnBasis

/-- Lengthening in the left tensor factor. -/
noncomputable def leftTensorLengthening :
    (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) →ₗ[ℚ]
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  TensorProduct.map unitLengthening
    (LinearMap.id : PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthSpace)

/-- Lengthening in the right tensor factor. -/
noncomputable def rightTensorLengthening :
    (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) →ₗ[ℚ]
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  TensorProduct.map
    (LinearMap.id : PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthSpace)
    unitLengthening

/-- The left deconcatenation defect. -/
noncomputable def leftDeconcatenationDefect :
    PositiveEdgeLengthSpace →ₗ[ℚ]
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  reducedDeconcatenation.comp unitLengthening -
    leftTensorLengthening.comp reducedDeconcatenation

/-- The right deconcatenation defect. -/
noncomputable def rightDeconcatenationDefect :
    PositiveEdgeLengthSpace →ₗ[ℚ]
      (PositiveEdgeLengthSpace ⊗[ℚ] PositiveEdgeLengthSpace) :=
  reducedDeconcatenation.comp unitLengthening -
    rightTensorLengthening.comp reducedDeconcatenation

/-- Exact endpoint-support formulas for the two deconcatenation defects. -/
def claim5284 : Prop :=
  ∀ ℓ : PositiveEdgeLength,
    leftDeconcatenationDefect (positiveEdgeVector ℓ) =
        positiveEdgeVector unitEdgeLength ⊗ₜ[ℚ] positiveEdgeVector ℓ ∧
      rightDeconcatenationDefect (positiveEdgeVector ℓ) =
        positiveEdgeVector ℓ ⊗ₜ[ℚ] positiveEdgeVector unitEdgeLength

end MathlibPlus.Open.Algebra
