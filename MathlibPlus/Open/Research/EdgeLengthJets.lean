import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators TensorProduct
noncomputable section

abbrev PositiveEdgeLength := {n : ℕ // 0 < n}
abbrev PositiveEdgeLengthSpace := PositiveEdgeLength →₀ ℚ
abbrev PositiveEdgeLengthTensor :=
  TensorProduct ℚ PositiveEdgeLengthSpace PositiveEdgeLengthSpace

def positiveEdgeBasis (l : PositiveEdgeLength) : PositiveEdgeLengthSpace :=
  Finsupp.single l 1

def positiveEdgeSuccessor (l : PositiveEdgeLength) : PositiveEdgeLength :=
  ⟨l.1 + 1, Nat.succ_pos _⟩

def positiveEdgeOne : PositiveEdgeLength :=
  ⟨1, by decide⟩

def positiveEdgeShift : PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthSpace :=
  Finsupp.lift PositiveEdgeLengthSpace ℚ PositiveEdgeLength
    (fun l => positiveEdgeBasis (positiveEdgeSuccessor l))

def positiveEdgeDeconcatenationOn (l : PositiveEdgeLength) : PositiveEdgeLengthTensor :=
  letI : Fintype {i : PositiveEdgeLength // i < l} := Fintype.ofFinite _
  ∑ i : {i : PositiveEdgeLength // i < l},
    TensorProduct.tmul ℚ (positiveEdgeBasis i.1)
      (positiveEdgeBasis ⟨l.1 - i.1.1, Nat.sub_pos_of_lt i.2⟩)

def positiveEdgeDeconcatenation :
    PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthTensor :=
  Finsupp.lift PositiveEdgeLengthTensor ℚ PositiveEdgeLength
    positiveEdgeDeconcatenationOn

def positiveEdgeShiftLeft :
    PositiveEdgeLengthTensor →ₗ[ℚ] PositiveEdgeLengthTensor :=
  TensorProduct.map positiveEdgeShift LinearMap.id

def positiveEdgeShiftRight :
    PositiveEdgeLengthTensor →ₗ[ℚ] PositiveEdgeLengthTensor :=
  TensorProduct.map LinearMap.id positiveEdgeShift

def positiveEdgeLambda :
    PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthTensor :=
  positiveEdgeDeconcatenation.comp positiveEdgeShift -
    positiveEdgeShiftLeft.comp positiveEdgeDeconcatenation

def positiveEdgeRho :
    PositiveEdgeLengthSpace →ₗ[ℚ] PositiveEdgeLengthTensor :=
  positiveEdgeDeconcatenation.comp positiveEdgeShift -
    positiveEdgeShiftRight.comp positiveEdgeDeconcatenation

/-- Claim 5379: the positive-length basis, shift, and reduced deconcatenation. -/
def positiveEdgeLengthSpaceAndReducedDeconcatenation : Prop :=
  ∀ l : PositiveEdgeLength,
    positiveEdgeShift (positiveEdgeBasis l) =
        positiveEdgeBasis (positiveEdgeSuccessor l) ∧
      positiveEdgeDeconcatenation (positiveEdgeBasis l) =
        positiveEdgeDeconcatenationOn l

/-- Claim 5380: the two endpoint commutator states. -/
def endpointCommutatorStates : Prop :=
  ∀ l : PositiveEdgeLength,
    positiveEdgeLambda (positiveEdgeBasis l) =
        TensorProduct.tmul ℚ (positiveEdgeBasis positiveEdgeOne)
          (positiveEdgeBasis l) ∧
      positiveEdgeRho (positiveEdgeBasis l) =
        TensorProduct.tmul ℚ (positiveEdgeBasis l)
          (positiveEdgeBasis positiveEdgeOne)

/-- Claim 5381: the finite, length-independent local jet relations. -/
def finiteSubdivisionJetRelations : Prop :=
  positiveEdgeDeconcatenation.comp positiveEdgeShift =
      positiveEdgeShiftLeft.comp positiveEdgeDeconcatenation + positiveEdgeLambda ∧
    positiveEdgeDeconcatenation.comp positiveEdgeShift =
      positiveEdgeShiftRight.comp positiveEdgeDeconcatenation + positiveEdgeRho ∧
    positiveEdgeLambda.comp positiveEdgeShift =
      positiveEdgeShiftRight.comp positiveEdgeLambda ∧
    positiveEdgeRho.comp positiveEdgeShift =
      positiveEdgeShiftLeft.comp positiveEdgeRho

end
end MathlibPlus.Open.Research
