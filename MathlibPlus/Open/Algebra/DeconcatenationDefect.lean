import Mathlib

namespace MathlibPlus.Open.Algebra

noncomputable section

/-- Positive integral edge lengths. -/
abbrev PositiveEdgeLength := {ℓ : ℕ // 0 < ℓ}

/-- The rational vector space spanned by positive integral edge lengths. -/
abbrev PositiveEdgeSpace := PositiveEdgeLength →₀ ℚ

/-- The ordered tensor square of the positive edge space. -/
abbrev OrderedPositiveEdgeTensor :=
  TensorProduct ℚ PositiveEdgeSpace PositiveEdgeSpace

/-- The basis vector of length `ℓ`. -/
def edgeBasis (ℓ : PositiveEdgeLength) : PositiveEdgeSpace :=
  Finsupp.single ℓ 1

/-- Successor of a positive edge length. -/
def edgeLengthSuccessor (ℓ : PositiveEdgeLength) : PositiveEdgeLength :=
  ⟨ℓ.1 + 1, by omega⟩

/-- Unit lengthening on basis vectors, extended linearly. -/
def unitLengthening : PositiveEdgeSpace →ₗ[ℚ] PositiveEdgeSpace :=
  Finsupp.lsum ℚ (fun ℓ =>
    LinearMap.toSpanSingleton ℚ PositiveEdgeSpace (edgeBasis (edgeLengthSuccessor ℓ)))

/-- Splitting a positive edge at every positive integral interior point. -/
def reducedDeconcatenationOnBasis
    (ℓ : PositiveEdgeLength) : OrderedPositiveEdgeTensor :=
  Finset.sum (Finset.univ : Finset (Fin (ℓ.1 - 1))) (fun i =>
    edgeBasis ⟨i.1 + 1, by omega⟩ ⊗ₜ[ℚ]
      edgeBasis ⟨ℓ.1 - (i.1 + 1), by omega⟩)

/-- Reduced edge deconcatenation, extended linearly from its basis values. -/
def reducedDeconcatenation :
    PositiveEdgeSpace →ₗ[ℚ] OrderedPositiveEdgeTensor :=
  Finsupp.lsum ℚ (fun ℓ =>
    LinearMap.toSpanSingleton ℚ OrderedPositiveEdgeTensor
      (reducedDeconcatenationOnBasis ℓ))

/-- Lengthening in the left tensor factor. -/
def leftTensorLengthening :
    OrderedPositiveEdgeTensor →ₗ[ℚ] OrderedPositiveEdgeTensor :=
  TensorProduct.map unitLengthening (LinearMap.id :
    PositiveEdgeSpace →ₗ[ℚ] PositiveEdgeSpace)

/-- Lengthening in the right tensor factor. -/
def rightTensorLengthening :
    OrderedPositiveEdgeTensor →ₗ[ℚ] OrderedPositiveEdgeTensor :=
  TensorProduct.map (LinearMap.id :
    PositiveEdgeSpace →ₗ[ℚ] PositiveEdgeSpace) unitLengthening

/-- The two deconcatenation-defect operators. -/
def leftDeconcatenationDefect :
    PositiveEdgeSpace →ₗ[ℚ] OrderedPositiveEdgeTensor :=
  reducedDeconcatenation.comp unitLengthening -
    leftTensorLengthening.comp reducedDeconcatenation

def rightDeconcatenationDefect :
    PositiveEdgeSpace →ₗ[ℚ] OrderedPositiveEdgeTensor :=
  reducedDeconcatenation.comp unitLengthening -
    rightTensorLengthening.comp reducedDeconcatenation

/-- The deconcatenation defects are defined by the left and right formulas. -/
def deconcatenationDefectOperators : Prop :=
  leftDeconcatenationDefect =
      reducedDeconcatenation.comp unitLengthening -
        leftTensorLengthening.comp reducedDeconcatenation ∧
    rightDeconcatenationDefect =
      reducedDeconcatenation.comp unitLengthening -
        rightTensorLengthening.comp reducedDeconcatenation

end

end MathlibPlus.Open.Algebra
