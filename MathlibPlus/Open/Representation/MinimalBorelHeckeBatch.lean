import MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f

noncomputable section

open scoped BigOperators
open UpperHalfPlane

namespace MathlibPlus.Open.Representation.MinimalBorelHeckeBatch

abbrev CoefficientFunction := ℍ → ℂ
abbrev CoefficientTensor := TensorProduct ℂ CoefficientFunction CoefficientFunction
abbrev CoefficientMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The exact Niemeier mass normalization used by the mass-paired coefficient model. -/
def niemeierMass : ℝ := 19971753984000 / 37092156523

/-- The two source class vectors before and after mass whitening. -/
def e0 : CoefficientFunction :=
  MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f.E12fun

def delta : CoefficientFunction :=
  MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f.Deltafun

def e1 : CoefficientFunction :=
  (Real.sqrt niemeierMass : ℂ) • delta

/-- The mass-whitened class carrier `span(E₁₂, √V_N Δ)`. -/
def classCarrier : Submodule ℂ CoefficientFunction :=
  Submodule.span ℂ ({e0, e1} : Set CoefficientFunction)

/-- Coordinate vectors for the ordered class basis `(e₀,e₁)`. -/
def coordinateUnit (i : Fin 2) : Fin 2 → ℂ :=
  fun j => if i = j then 1 else 0

/-- The transported bilinear mass pairing on coefficient coordinates. -/
def massPairing (u v : Fin 2 → ℂ) : ℂ :=
  ∑ i : Fin 2, u i * v i

/-- Contract the second tensor factor against the transported mass pairing. -/
def massContraction (A : CoefficientMatrix) : CoefficientMatrix :=
  fun i j => ∑ k : Fin 2, A i k * massPairing (coordinateUnit k) (coordinateUnit j)

def classBasisVector (i : Fin 2) : CoefficientFunction :=
  if i = 0 then e0 else e1

/-- Reassemble a coefficient matrix as a tensor in the actual source carrier. -/
def coefficientTensor (A : CoefficientMatrix) : CoefficientTensor :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    A i j • TensorProduct.tmul ℂ (classBasisVector i) (classBasisVector j)

/-- The diagonal Klingen boundary tensor before whitening. -/
def diagonalKlingenTensor (α : ℂ) : CoefficientTensor :=
  TensorProduct.tmul ℂ e0 delta +
    TensorProduct.tmul ℂ delta e0 +
    α • TensorProduct.tmul ℂ delta delta

/-- The tensor after the stated multiplication by `√V_N`. -/
def whitenedKlingenTensor (α : ℂ) : CoefficientTensor :=
  (Real.sqrt niemeierMass : ℂ) • diagonalKlingenTensor α

/-- The coefficient matrix obtained from the stated `(e₀,e₁)` expansion. -/
def klingenCoefficientMatrix (α : ℂ) : CoefficientMatrix :=
  !![0, 1; 1, α / (Real.sqrt niemeierMass : ℂ)]

/-- The exchange and cusp-projector matrices in the ordered mass-whitened basis. -/
def coefficientX : CoefficientMatrix :=
  !![0, 1; 1, 0]

def coefficientZ : CoefficientMatrix :=
  !![1, 0; 0, -1]

def cuspProjector : CoefficientMatrix :=
  ((2 : ℂ)⁻¹) • ((1 : CoefficientMatrix) - coefficientZ)

/-- Claim 14796: the actual diagonal Klingen tensor, its mass whitening, and
its bilinear middle-coordinate contraction give `X + κ P₋`, with
`κ = α / √V_N`; the free diagonal coefficient is confined to the cusp line. -/
def claim14796 : Prop :=
  (e0 = MathlibPlus.Open.Analysis.K0028CoreBatch019ffe1f.E12fun ∧
    e1 = (Real.sqrt niemeierMass : ℂ) • delta ∧
    classCarrier = Submodule.span ℂ ({e0, e1} : Set CoefficientFunction) ∧
    (∀ i j : Fin 2,
      massPairing (coordinateUnit i) (coordinateUnit j) =
        if i = j then 1 else 0)) ∧
  ∀ α : ℂ,
    whitenedKlingenTensor α = coefficientTensor (klingenCoefficientMatrix α) ∧
    massContraction (klingenCoefficientMatrix α) =
      coefficientX + (α / (Real.sqrt niemeierMass : ℂ)) • cuspProjector

end MathlibPlus.Open.Representation.MinimalBorelHeckeBatch

end
