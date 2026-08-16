import Mathlib

namespace MathlibPlus.Open.AlgebraicPauli

noncomputable section

/-- The carrier `Sym^k (ℂ²)`, with its weight-indexed basis supplied as data. -/
abbrev SymPower (k : ℕ) :=
  SymmetricPower ℂ (Fin k) (Fin 2 → ℂ)

abbrev WeightBasis (k : ℕ) :=
  Module.Basis (Fin (k + 1)) ℂ (SymPower k)

abbrev MixedSpace (k : ℕ) :=
  TensorProduct ℂ (SymPower k) (SymPower k)

abbrev MixedBasis (k : ℕ) (b : WeightBasis k) :
    Module.Basis (Fin (k + 1) × Fin (k + 1)) ℂ (MixedSpace k) :=
  b.tensorProduct b

def character (k : ℕ) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (k + 1))
    (fun r => z ^ ((k : ℤ) - 2 * (r : ℤ)))

def diagonalAction (k : ℕ) (b : WeightBasis k) (z : ℂ) :
    SymPower k →ₗ[ℂ] SymPower k :=
  (b.constr ℂ)
    (fun r => z ^ ((k : ℤ) - 2 * (r : ℤ)) • b r)

def mixedAction (k : ℕ) (b : WeightBasis k) (y α : ℂ) :
    MixedSpace k →ₗ[ℂ] MixedSpace k :=
  TensorProduct.map (diagonalAction k b y) (diagonalAction k b α)

def equalAlignmentProjector (k : ℕ) (b : WeightBasis k) :
    MixedSpace k →ₗ[ℂ] MixedSpace k :=
  ((MixedBasis k b).constr ℂ)
    (fun ij => if ij.1 = ij.2 then MixedBasis k b ij else 0)

def oppositeAlignmentProjector (k : ℕ) (b : WeightBasis k) :
    MixedSpace k →ₗ[ℂ] MixedSpace k :=
  ((MixedBasis k b).constr ℂ)
    (fun ij =>
      if ij.2 = Fin.rev ij.1 then MixedBasis k b ij else 0)

def mixedTrace (k : ℕ) (b : WeightBasis k)
    (f : MixedSpace k →ₗ[ℂ] MixedSpace k) : ℂ :=
  Matrix.trace ((LinearMap.toMatrix (MixedBasis k b) (MixedBasis k b)) f)

def traceAfterAlignment (k : ℕ) (b : WeightBasis k) (y α : ℂ)
    (q : MixedSpace k →ₗ[ℂ] MixedSpace k) : ℂ :=
  mixedTrace k b ((mixedAction k b y α).comp q)

/-- Claim 11811: the two inserted traces recover the two oriented contractions. -/
def alignmentContractions : Prop :=
  ∀ (k : ℕ) (b : WeightBasis k) (y α : ℂ),
    traceAfterAlignment k b y α (equalAlignmentProjector k b) =
        character k (y * α) ∧
      traceAfterAlignment k b y α (oppositeAlignmentProjector k b) =
        character k (y * α⁻¹)

def oddCurrentRightHandSide (k : ℕ) (U Φ : ℝ) : ℂ :=
  Complex.ofReal
    (Finset.sum (Finset.Icc 1 k) (fun j =>
      Finset.sum (Finset.Icc 1 j) (fun m =>
        Real.sinh ((m : ℝ) * U) * Real.sin ((m : ℝ) * Φ))))

/-- Claim 11813: the odd current has its stated finite character expansion. -/
def oddCurrentCharacterIdentity : Prop :=
  ∀ (k : ℕ) (U Φ : ℝ),
    let y := Complex.exp ((U : ℂ) / 2)
    let α := Complex.exp (Complex.I * (Φ : ℂ) / 2)
    (character k (y * α) ^ 2 - character k (y * α⁻¹) ^ 2) /
          (4 * Complex.I) =
      oddCurrentRightHandSide k U Φ

def relativeOddCoordinate (k : ℕ) (b : WeightBasis k) (y α : ℂ) :
    MixedSpace k →ₗ[ℂ] MixedSpace k :=
  (1 / 4 : ℂ) •
    TensorProduct.map
      (diagonalAction k b y - diagonalAction k b y⁻¹)
      (diagonalAction k b α - diagonalAction k b α⁻¹)

def ordinaryTrace (k : ℕ) (b : WeightBasis k) (y α : ℂ) : ℂ :=
  mixedTrace k b (mixedAction k b y α)

def relativeOddTrace (k : ℕ) (b : WeightBasis k) (y α : ℂ) : ℂ :=
  mixedTrace k b (relativeOddCoordinate k b y α)

/-- Claim 11817: the ordinary trace loses orientation, including its degree-one
and degree-two comparison identities. -/
def ordinaryScalarTraceErasesOrientation : Prop :=
  (∀ (k : ℕ) (b : WeightBasis k) (y α : ℂ),
    ordinaryTrace k b y α = character k y * character k α ∧
      relativeOddTrace k b y α = 0) ∧
  (∀ (y α : ℂ),
    character 1 y * character 1 α =
        character 1 (y * α) + character 1 (y * α⁻¹) ∧
      character 2 y * character 2 α -
          character 2 (y * α) - character 2 (y * α⁻¹) =
        y ^ (2 : ℤ) + y ^ (-2 : ℤ) +
            α ^ (2 : ℤ) + α ^ (-2 : ℤ) - 1)

end
end MathlibPlus.Open.AlgebraicPauli
