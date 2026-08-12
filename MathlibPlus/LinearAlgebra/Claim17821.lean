import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim17821

/-- The exact rank-two completed checkerboard determinant from claim 17821.
The four entries `h₀`, ..., `h₃` are kept explicit because the source does
not impose a particular sequence type. -/
theorem exactRankTwoBezoutDeterminant {R : Type*} [CommRing R]
    (h₀ h₁ h₂ h₃ : R) :
    let C : Matrix (Fin 2) (Fin 2) R :=
      !![h₀ * h₁, 2 * h₀ * h₂;
         2 * h₀ * h₂, 3 * h₀ * h₃ + h₁ * h₂]
    Matrix.det C =
      3 * h₀ ^ 2 * h₁ * h₃ + h₀ * h₁ ^ 2 * h₂ - 4 * h₀ ^ 2 * h₂ ^ 2 := by
  dsimp
  rw [Matrix.det_fin_two]
  simp [Matrix.cons_val']
  ring

end MathlibPlus.LinearAlgebra.Claim17821
