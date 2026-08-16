import MathlibPlus.Open.AlgebraicPauli

open scoped Matrix

namespace MathlibPlus.Open.Representation.O0173Pauli

open MathlibPlus.Open.AlgebraicPauli

noncomputable section

abbrev CoefficientAlgebra := EndC

def Pplus : CoefficientAlgebra := (2 : ℂ)⁻¹ • (one + Z)

def cuspColumnProjection : CoefficientAlgebra →ₗ[ℂ] CoefficientAlgebra :=
  LinearMap.mulRight ℂ Pminus

def cuspScalarCoefficient : CoefficientAlgebra →ₗ[ℂ] ℂ :=
  (Matrix.traceLinearMap (Fin 2) ℂ ℂ).comp
    (LinearMap.mulLeft ℂ (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)))

def diagonalClassChannel (pE pΔ : ℂ) :
    CoefficientAlgebra →ₗ[ℂ] CoefficientAlgebra :=
  LinearMap.mulRight ℂ (pE • Pplus + pΔ • Pminus)

/-- Claim 14802: right multiplication by the cusp projector keeps one column,
with the stated Pauli actions, rank, kernel, scalar rank, and reconstruction
obstruction. -/
def claim14802 : Prop :=
  (one * Pminus = Pminus ∧
    Z * Pminus = -Pminus ∧
    X * Pminus = E01 ∧
    iY * Pminus = E01) ∧
    LinearMap.ker cuspColumnProjection =
      Submodule.span ℂ ({one + Z, X - iY} : Set CoefficientAlgebra) ∧
    Set.range cuspColumnProjection =
      {B : CoefficientAlgebra | ∃ a b : ℂ,
        B = a • Pminus + b • E01} ∧
    Module.finrank ℂ CoefficientAlgebra = 4 ∧
    Module.finrank ℂ (LinearMap.range cuspColumnProjection) = 2 ∧
    (∀ B : CoefficientAlgebra, cuspScalarCoefficient B = B 1 1) ∧
    Module.finrank ℂ (LinearMap.range cuspScalarCoefficient) = 1 ∧
    ¬ ∃ post : CoefficientAlgebra → CoefficientAlgebra,
      Function.LeftInverse post cuspColumnProjection

/-- Claim 14803: at each point of a two-column diagonal class channel, the
full Pauli frame is preserved exactly when both diagonal entries are nonzero. -/
def claim14803 : Prop :=
  ∀ (pE pΔ : ℂ),
    Function.Injective (diagonalClassChannel pE pΔ) ↔ pE * pΔ ≠ 0

end

end MathlibPlus.Open.Representation.O0173Pauli
