import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.Claim14739

noncomputable section

/-- The finite-heat scalar row in the concrete split/compact real-variable bases. -/
def finiteHeatRow (x lam g σ : ℝ) : ℝ → ℝ → ℂ :=
  let d : ℝ := 2 + x
  let κ : ℝ := lam * g
  fun U Φ =>
    (d : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ) +
      (σ * κ : ℂ) * (Real.sinh U : ℂ) * (Real.sin Φ : ℂ)

/-- Record 12's coefficient matrix for the finite-heat scalar row. -/
def finiteHeatCoefficientMatrix (x lam g σ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let d : ℝ := 2 + x
  let κ : ℝ := lam * g
  !![0, -2, 0; (d : ℂ), 0, 0; 0, 0, (σ * κ : ℂ)]

/-- The fixed split basis from the reviewed separation-rank carrier. -/
def splitBasis : Fin 3 → ℝ → ℂ := fun i =>
  if i = 0 then (fun _ => 1)
  else if i = 1 then (fun U => Real.cosh U)
  else fun U => Real.sinh U

/-- The fixed compact basis from the reviewed separation-rank carrier. -/
def compactBasis : Fin 3 → ℝ → ℂ := fun j =>
  if j = 0 then (fun _ => 1)
  else if j = 1 then (fun Φ => Real.cos Φ)
  else fun Φ => Real.sin Φ

/-- Evaluation of a coefficient matrix in those two displayed bases. -/
def coefficientEvaluation (M : Matrix (Fin 3) (Fin 3) ℂ) : ℝ → ℝ → ℂ :=
  fun U Φ => ∑ i, ∑ j, splitBasis i U * M i j * compactBasis j Φ

/-- The minimum number of arbitrary separated complex-valued summands. -/
def separationRank (R : ℝ → ℝ → ℂ) : ℕ :=
  sInf {n : ℕ | ∃ f : Fin n → ℝ → ℂ, ∃ h : Fin n → ℝ → ℂ,
    ∀ U Φ, R U Φ = ∑ j, f j U * h j Φ}

/-- Claim 14739: the scalar row has the displayed determinant and exact ranks. -/
def claim14739 : Prop :=
  ∀ x lam g : ℝ, 0 < 2 + x →
    ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      let d : ℝ := 2 + x
      let κ : ℝ := lam * g
      let R : ℝ → ℝ → ℂ := finiteHeatRow x lam g σ
      let M : Matrix (Fin 3) (Fin 3) ℂ :=
        finiteHeatCoefficientMatrix x lam g σ
      (∀ U Φ : ℝ, R U Φ = coefficientEvaluation M U Φ) ∧
        separationRank R = Matrix.rank M ∧
        Matrix.det M = 2 * (σ : ℂ) * (d : ℂ) * (κ : ℂ) ∧
        (κ ≠ 0 → Matrix.rank M = 3 ∧ separationRank R = 3) ∧
        (κ = 0 → Matrix.rank M = 2 ∧ separationRank R = 2)

end

end MathlibPlus.Open.ResearchFormalization.Claim14739
