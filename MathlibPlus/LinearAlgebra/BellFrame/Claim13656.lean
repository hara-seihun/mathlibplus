import Mathlib

namespace MathlibPlus.LinearAlgebra.BellFrame.Claim13656

/-- Claim 13656 with the standard row-major vectorization order `(00,01,10,11)`. -/
def bellFrameCoordinates_claim13656 : Prop :=
  let rvec : Matrix (Fin 2) (Fin 2) ℂ → (Fin 4 → ℂ) := fun A =>
    ![A 0 0, A 0 1, A 1 0, A 1 1]
  let Id : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let iY : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • Y
  let c : ℂ := (1 / Real.sqrt 2 : ℝ)
  let Φplus : Fin 4 → ℂ := c • ![1, 0, 0, 1]
  let Ψplus : Fin 4 → ℂ := c • ![0, 1, 1, 0]
  let Φminus : Fin 4 → ℂ := c • ![1, 0, 0, -1]
  let Ψminus : Fin 4 → ℂ := c • ![0, 1, -1, 0]
  Φplus = c • rvec Id ∧
    Ψplus = c • rvec X ∧
    Φminus = c • rvec Z ∧
    Ψminus = c • rvec iY

/-- The scalar-plus-adjoint Bell decomposition of `End(ℂ²)`. -/
def pauliFrameDecomposition_claim13656 : Prop :=
  let Id : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
  let X : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let Y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
  let iY : Matrix (Fin 2) (Fin 2) ℂ := Complex.I • Y
  let Z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  (∀ (a₀ a₁ a₂ a₃ : ℂ),
    a₀ • Id + a₁ • X + a₂ • iY + a₃ • Z = 0 →
      a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0) ∧
    (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
      ∃ (a₀ a₁ a₂ a₃ : ℂ),
        A = a₀ • Id + a₁ • X + a₂ • iY + a₃ • Z)

end MathlibPlus.LinearAlgebra.BellFrame.Claim13656
