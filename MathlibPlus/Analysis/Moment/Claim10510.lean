import Mathlib

namespace MathlibPlus.Analysis.Moment.Claim10510

/-- The rank-two and rank-three determinant factors for the gamma moments
`hⱼ = (α)ⱼ/(2j)!`, as stated in claim 10510. -/
theorem gammaRankTwoAndThreeDeterminants (α : ℝ) (_hα : 0 < α) :
    let h₀ : ℝ := 1
    let h₁ : ℝ := α / 2
    let h₂ : ℝ := α * (α + 1) / 24
    let h₃ : ℝ := α * (α + 1) * (α + 2) / 720
    let h₄ : ℝ := α * (α + 1) * (α + 2) * (α + 3) / 40320
    let h₅ : ℝ := α * (α + 1) * (α + 2) * (α + 3) * (α + 4) / 3628800
    let C₂ : Matrix (Fin 2) (Fin 2) ℝ :=
      !![h₀ * h₁, 2 * h₀ * h₂;
         2 * h₀ * h₂, 3 * h₀ * h₃ + h₁ * h₂]
    let C₃ : Matrix (Fin 3) (Fin 3) ℝ :=
      !![h₀ * h₁, 2 * h₀ * h₂, 3 * h₀ * h₃;
         2 * h₀ * h₂, 3 * h₀ * h₃ + h₁ * h₂, 4 * h₀ * h₄ + 2 * h₁ * h₃;
         3 * h₀ * h₃, 4 * h₀ * h₄ + 2 * h₁ * h₃,
           5 * h₀ * h₅ + 3 * h₁ * h₄ + h₂ * h₃]
    Matrix.det C₂ = α ^ 2 * (α + 1) * (2 * α - 1) / 360 ∧
      Matrix.det C₃ =
        α ^ 3 * (α + 1) ^ 2 * (α + 2) * (2 * α - 3) *
          (2 * α - 1) ^ 2 / 285768000 := by
  dsimp
  constructor
  · rw [Matrix.det_fin_two]
    simp [Matrix.cons_val']
    ring
  · rw [Matrix.det_fin_three]
    simp (discharger := decide) [Matrix.cons_val']
    ring

end MathlibPlus.Analysis.Moment.Claim10510
