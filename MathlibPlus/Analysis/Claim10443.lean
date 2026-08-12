import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace MathlibPlus.Analysis.Claim10443

noncomputable section

/-- At `s = 0`, the MacWilliams coordinate change and the zeta reflection
coordinate change have the distinct values recorded in claim 10443. -/
theorem macWilliamsNotZetaReflectionAtZero
    {p : ℕ} (hp : p.Prime) :
    let u : ℝ → ℝ := fun s => (p : ℝ) ^ (-s)
    let macWilliams : ℝ → ℝ := fun s => (1 - u s) / (1 + u s)
    let zetaReflection : ℝ → ℝ := fun s => (p : ℝ) ^ (-(1 - s))
    macWilliams 0 = 0 ∧
      zetaReflection 0 = (p : ℝ)⁻¹ ∧
      macWilliams 0 ≠ zetaReflection 0 := by
  dsimp
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hu : (p : ℝ) ^ (-(0 : ℝ)) = 1 := by
    simp
  have href : (p : ℝ) ^ (-(1 - (0 : ℝ))) = (p : ℝ)⁻¹ := by
    rw [show (-(1 - (0 : ℝ))) = (-1 : ℝ) by norm_num]
    rw [Real.rpow_neg (le_of_lt hp0), Real.rpow_one]
  rw [hu, href]
  constructor
  · norm_num
  constructor
  · rfl
  · intro h
    have : (p : ℝ)⁻¹ = 0 := by simpa using h.symm
    exact inv_ne_zero hpne this

end
end MathlibPlus.Analysis.Claim10443
