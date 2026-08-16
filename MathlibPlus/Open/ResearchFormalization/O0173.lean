import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.O0173

/-- The two named weight-12 class lines in the source's ordered basis. -/
abbrev ClassLine := Fin 2

def eisenstein12 : ClassLine := 0
def delta : ClassLine := 1

abbrev ClassVector := ClassLine → ℂ
abbrev ClassTensor := ClassLine → ClassLine → ℂ
abbrev CoefficientMatrix := Matrix ClassLine ClassLine ℂ

/-- A coordinate vector in the named class-line carrier. -/
def classBasis (i : ClassLine) : ClassVector :=
  fun j => if j = i then 1 else 0

/-- The first whitened class vector is the Eisenstein series E₁₂. -/
def eEisenstein : ClassVector := classBasis eisenstein12

/-- The second whitened class vector is e₁ = √V_N Δ. -/
def eMassDelta : ClassVector := classBasis delta

/-- The mass-whitened bilinear form is bilinear, not Hermitian. -/
def massBilinear (u v : ClassVector) : ℂ :=
  ∑ i : ClassLine, u i * v i

/-- Contracting the second class factor against the mass form identifies a
class tensor with its coefficient endomorphism. -/
def contractClassTensor (T : ClassTensor) : CoefficientMatrix :=
  fun i j => ∑ k : ClassLine, T i k * massBilinear (classBasis k) (classBasis j)

/-- A pure class tensor in the ordered (E₁₂, √V_N Δ) basis. -/
def pureClassTensor (u v : ClassVector) : ClassTensor :=
  fun i j => u i * v j

/-- The mass-whitened contracted Klingen tensor from the source. -/
def klingenClassTensor (κ : ℂ) : ClassTensor :=
  pureClassTensor eEisenstein eMassDelta +
    pureClassTensor eMassDelta eEisenstein +
    κ • pureClassTensor eMassDelta eMassDelta

/-- Its coefficient matrix, before applying the Hecke-parity projection. -/
def klingenCoefficientMatrix (κ : ℂ) : CoefficientMatrix :=
  contractClassTensor (klingenClassTensor κ)

/-- The Pauli matrices on the named ordered class-line carrier. -/
def coefficientX : CoefficientMatrix :=
  fun i j =>
    if i = eisenstein12 ∧ j = delta then 1
    else if i = delta ∧ j = eisenstein12 then 1
    else 0

def coefficientY : CoefficientMatrix :=
  fun i j =>
    if i = eisenstein12 ∧ j = delta then -Complex.I
    else if i = delta ∧ j = eisenstein12 then Complex.I
    else 0

def coefficientI : CoefficientMatrix := 1

def coefficientZ : CoefficientMatrix :=
  fun i j =>
    if i = j then
      if i = eisenstein12 then 1 else -1
    else 0

/-- The source's `iY` axis. -/
def coefficientIY : CoefficientMatrix := (Complex.I : ℂ) • coefficientY

/-- The cusp projector P₋ = (I − Z)/2. -/
def coefficientPMinus : CoefficientMatrix :=
  ((2 : ℂ)⁻¹) • (coefficientI - coefficientZ)

/-- Hecke-odd projection by conjugation with the normalized Hecke grading Z. -/
def heckeOddProjection (B : CoefficientMatrix) : CoefficientMatrix :=
  ((2 : ℂ)⁻¹) • (B - coefficientZ * B * coefficientZ)

/-- The coefficient of E₁₂ ⊗ √V_N Δ in a coefficient matrix. -/
def symmetricCrossCoefficient (B : CoefficientMatrix) : ℂ :=
  B eisenstein12 delta

/-- Both ordered cross entries have the normalized symmetric coefficient one. -/
def normalizedSymmetricCrossCoefficient (B : CoefficientMatrix) : Prop :=
  symmetricCrossCoefficient B = 1 ∧ B delta eisenstein12 = 1

/-- Claim 14797: the contracted Klingen kernel has the prime-independent
Hecke-odd symmetric axis X, with the full odd plane, transpose selections,
and normalized-axis uniqueness stated on the named class carrier. -/
def claim14797 : Prop :=
  (∀ κ : ℂ, heckeOddProjection (klingenCoefficientMatrix κ) = coefficientX) ∧
    (∀ B : CoefficientMatrix,
      coefficientZ * B * coefficientZ = -B ↔
        ∃ a b : ℂ, B = a • coefficientX + b • coefficientIY) ∧
    (∀ B : CoefficientMatrix,
      coefficientZ * B * coefficientZ = -B →
        coefficientX.transpose = coefficientX ∧
        coefficientIY.transpose = -coefficientIY ∧
        ((B.transpose = B) ↔ ∃ a : ℂ, B = a • coefficientX) ∧
        ((B.transpose = -B) ↔ ∃ b : ℂ, B = b • coefficientIY)) ∧
    (∀ B : CoefficientMatrix,
      coefficientZ * B * coefficientZ = -B →
        B.transpose = B →
        normalizedSymmetricCrossCoefficient B →
        B = coefficientX)

end MathlibPlus.Open.ResearchFormalization.O0173
