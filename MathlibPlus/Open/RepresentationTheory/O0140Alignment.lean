import MathlibPlus.Open.Research.FormalizationBatch_01a00bf2_OrthogonalReflectionCompression
import MathlibPlus.Open.AlgebraicPauli
import MathlibPlus.Open.AlgebraicPauli.Orientation

namespace MathlibPlus.Open.RepresentationTheory.O0140Alignment

open MathlibPlus.Open.Research.FormalizationBatch_01a00bf2

noncomputable section

abbrev AlignmentSpace (k : ℕ) := M k
abbrev AlignmentBasis (k : ℕ) (b : WeightBasis k) := MixedBasis k b

def alignmentDiagonalAction (k : ℕ) (b : WeightBasis k) (z : ℂ) :
    V k →ₗ[ℂ] V k :=
  b.constr ℂ (fun r => z ^ ((k : ℤ) - 2 * (r : ℤ)) • b r)

def alignmentMixedAction (k : ℕ) (b : WeightBasis k) (y α : ℂ) :
    AlignmentSpace k →ₗ[ℂ] AlignmentSpace k :=
  TensorProduct.map (alignmentDiagonalAction k b y)
    (alignmentDiagonalAction k b α)

def alignmentEqualProjector (k : ℕ) (b : WeightBasis k) :
    AlignmentSpace k →ₗ[ℂ] AlignmentSpace k :=
  (AlignmentBasis k b).constr ℂ
    (fun ij => if ij.1 = ij.2 then AlignmentBasis k b ij else 0)

def alignmentOppositeProjector (k : ℕ) (b : WeightBasis k) :
    AlignmentSpace k →ₗ[ℂ] AlignmentSpace k :=
  (AlignmentBasis k b).constr ℂ
    (fun ij =>
      if ij.2 = Fin.rev ij.1 then AlignmentBasis k b ij else 0)

def alignmentTrace (k : ℕ) (b : WeightBasis k)
    (f : AlignmentSpace k →ₗ[ℂ] AlignmentSpace k) : ℂ :=
  Matrix.trace ((LinearMap.toMatrix (AlignmentBasis k b) (AlignmentBasis k b)) f)

def alignmentConjugate {k : ℕ}
    (g q : AlignmentSpace k →ₗ[ℂ] AlignmentSpace k) :
    AlignmentSpace k →ₗ[ℂ] AlignmentSpace k :=
  g * q * g

def alignmentOperatorSpan (k : ℕ) (b : WeightBasis k) :
    Submodule ℂ (AlignmentSpace k →ₗ[ℂ] AlignmentSpace k) :=
  Submodule.span ℂ
    {alignmentEqualProjector k b, alignmentOppositeProjector k b}

def alignmentTrivialLine (k : ℕ) (b : WeightBasis k) :
    Submodule ℂ (AlignmentSpace k →ₗ[ℂ] AlignmentSpace k) :=
  Submodule.span ℂ
    {alignmentEqualProjector k b + alignmentOppositeProjector k b}

def alignmentRelativeLine (k : ℕ) (b : WeightBasis k) :
    Submodule ℂ (AlignmentSpace k →ₗ[ℂ] AlignmentSpace k) :=
  Submodule.span ℂ
    {alignmentEqualProjector k b + (-1 : ℂ) • alignmentOppositeProjector k b}

def alignmentCentralZeroWeightLine (k : ℕ) (b : WeightBasis k) :
    Submodule ℂ (AlignmentSpace k) :=
  Submodule.span ℂ
    {x | ∃ r : Fin (k + 1), Fin.rev r = r ∧ x = AlignmentBasis k b (r, r)}

def twoAlignmentIndependent {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (A B : E) : Prop :=
  ∀ a c : ℂ, a • A + c • B = 0 → a = 0 ∧ c = 0

def alignmentPermutationModule (k : ℕ) (b : WeightBasis k) : Prop :=
  let S := factorSwap k
  let R_h := leftReversal k b
  let R_c := rightReversal k b
  let D := longestOperator k b
  let Qplus := alignmentEqualProjector k b
  let Qminus := alignmentOppositeProjector k b
  let qsum := Qplus + Qminus
  let qdiff := Qplus + (-1 : ℂ) • Qminus
  alignmentConjugate S Qplus = Qplus ∧
    alignmentConjugate S Qminus = Qminus ∧
    alignmentConjugate D Qplus = Qplus ∧
    alignmentConjugate D Qminus = Qminus ∧
    alignmentConjugate R_h Qplus = Qminus ∧
    alignmentConjugate R_h Qminus = Qplus ∧
    alignmentConjugate R_c Qplus = Qminus ∧
    alignmentConjugate R_c Qminus = Qplus ∧
    twoAlignmentIndependent Qplus Qminus ∧
    Module.finrank ℂ (alignmentOperatorSpan k b) = 2 ∧
    alignmentOperatorSpan k b =
      alignmentTrivialLine k b ⊔ alignmentRelativeLine k b ∧
    alignmentTrivialLine k b ⊓ alignmentRelativeLine k b = ⊥ ∧
    Module.finrank ℂ (alignmentTrivialLine k b) = 1 ∧
    Module.finrank ℂ (alignmentRelativeLine k b) = 1 ∧
    alignmentConjugate S qsum = qsum ∧
    alignmentConjugate D qsum = qsum ∧
    alignmentConjugate R_h qsum = qsum ∧
    alignmentConjugate R_c qsum = qsum ∧
    alignmentConjugate S qdiff = qdiff ∧
    alignmentConjugate D qdiff = qdiff ∧
    alignmentConjugate R_h qdiff = (-1 : ℂ) • qdiff ∧
    alignmentConjugate R_c qdiff = (-1 : ℂ) • qdiff

/-- Claim 14753: the two exact alignment contractions and their positive-degree
trivial/relative two-point permutation module. -/
def claim14753 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (b : WeightBasis k) (y α : ℂ),
    let T := alignmentMixedAction k b y α
    let Qplus := alignmentEqualProjector k b
    let Qminus := alignmentOppositeProjector k b
    alignmentTrace k b (T * Qplus) =
        MathlibPlus.Open.AlgebraicPauli.character k (y * α) ∧
      alignmentTrace k b (T * Qminus) =
        MathlibPlus.Open.AlgebraicPauli.character k (y * α⁻¹) ∧
      alignmentPermutationModule k b

/-- Claim 14766: the alignment projectors carry the quotient character and
have the stated Arthur-compressed ranks, including the even-degree central line. -/
def claim14766 : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (b : WeightBasis k),
    let Qplus := alignmentEqualProjector k b
    let Qminus := alignmentOppositeProjector k b
    let PiPlus := arthurProjector k b
    let a : ℕ := (k + 2) / 2
    alignmentPermutationModule k b ∧
      Module.finrank ℂ (LinearMap.range (PiPlus * Qplus * PiPlus)) = a ∧
      Module.finrank ℂ (LinearMap.range (PiPlus * Qminus * PiPlus)) = a ∧
      (if Even k then
        LinearMap.range Qplus ⊓ LinearMap.range Qminus =
          alignmentCentralZeroWeightLine k b
       else True)

end
end MathlibPlus.Open.RepresentationTheory.O0140Alignment
