import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatch

noncomputable def normalizedSineDenominator (y : ℝ) : ℝ :=
  if y = 0 then 1 else Real.sinh (2 * Real.pi * y) / (2 * Real.pi * y)

noncomputable def normalizedRowFactor (z : ℂ) : ℂ :=
  Complex.sin (Complex.ofReal Real.pi * z) /
    Complex.ofReal (Real.sqrt (normalizedSineDenominator z.im))

noncomputable def lowerScaledTanh (y : ℝ) : ℝ :=
  Real.pi * |y| * Real.tanh (Real.pi * |y|)

noncomputable def upperScaledCoth (y : ℝ) : ℝ :=
  if y = 0 then 1
  else Real.pi * |y| *
    (Real.cosh (Real.pi * |y|) / Real.sinh (Real.pi * |y|))

/-- Claim 15162: the explicitly normalized sine row factor has the stated bounds. -/
def normalizedRowFactorBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ x y : ℝ,
      lowerScaledTanh y ≤ ‖normalizedRowFactor (Complex.ofReal x + Complex.ofReal y * Complex.I)‖ ^ 2 ∧
        ‖normalizedRowFactor (Complex.ofReal x + Complex.ofReal y * Complex.I)‖ ^ 2 ≤
          upperScaledCoth y ∧
            upperScaledCoth y ≤ C * (1 + |y|)

noncomputable def movingActionConstant (a : ℝ → ℝ) (L : ℝ) : ℝ :=
  (5 : ℝ) / 2 - Real.log (a L) / L

/-- Claim 15174: the moving action constant has the stated eventual bounds. -/
def movingActionConstantBounds (a : ℝ → ℝ) (y₀ y₁ : ℝ) : Prop :=
  (0 < y₀ ∧ y₀ < y₁ ∧ y₁ < (1 : ℝ) / 2) →
    (∀ L : ℝ, 1 ≤ a L) →
      Filter.Tendsto (fun L : ℝ => a L * Real.exp (-2 * L)) Filter.atTop (nhds 0) →
        ((∃ error : ℝ → ℝ,
            Filter.Tendsto error Filter.atTop (nhds 0) ∧
              ∀ᶠ L : ℝ in Filter.atTop,
                (1 : ℝ) / 2 + error L < movingActionConstant a L) ∧
          (∀ᶠ L : ℝ in Filter.atTop,
            movingActionConstant a L ≤ (5 : ℝ) / 2) ∧
          (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
            ∀ᶠ L : ℝ in Filter.atTop,
              ∀ y : ℝ, y₀ ≤ y → y ≤ y₁ →
                c ≤ movingActionConstant a L - y ∧
                  movingActionConstant a L - y ≤ C))

end MathlibPlus.Open.Analysis.FormalizationBatch
