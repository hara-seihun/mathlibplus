import Mathlib
import MathlibPlus.Analysis.Claim13736And19168
import MathlibPlus.Analysis.HilleHardyLorentzAtom
import MathlibPlus.LinearAlgebra.ExteriorSquareDeterminant

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0246Repair

noncomputable section

/-- The normalized Hille--Hardy Lorentz atom. -/
def lorentzAtom (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh ξ, Real.sinh ξ; Real.sinh ξ, Real.cosh ξ]

/-- The exchange-exterior generator in the two internal-parity coordinates. -/
def exchangeExteriorGenerator : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 1 ∧ j = 0 then -1
    else 0

/-- Tensoring the same atom on both factors. -/
def tensorAtomAction (ξ : ℝ)
    (X : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun i j => ∑ k, ∑ l,
    lorentzAtom ξ i k * lorentzAtom ξ j l * X k l

/-- The one-atom Schur defect retained by internal reduction. -/
def schurDefect (ξ : ℝ) : ℝ :=
  Real.cosh ξ - Real.sinh ξ ^ 2 / Real.cosh ξ

/-- Claim 19169: tensoring determinant-one atoms and then taking the
exchange-exterior line has eigenvalue one, whereas the strict one-atom Schur
margin is retained only by reducing before that fusion/projection. -/
def claim19169_internalReductionExchangeProjectionOrder : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Matrix.det (lorentzAtom ξ) = 1 ∧
      tensorAtomAction ξ exchangeExteriorGenerator =
        exchangeExteriorGenerator ∧
      schurDefect ξ = 1 / Real.cosh ξ ∧
      0 < schurDefect ξ ∧
      (1 : ℝ) ≠ schurDefect ξ ∧
      tensorAtomAction ξ exchangeExteriorGenerator ≠
        (fun i j => schurDefect ξ * exchangeExteriorGenerator i j)

end

end MathlibPlus.Open.NewResearch2.R0246Repair
