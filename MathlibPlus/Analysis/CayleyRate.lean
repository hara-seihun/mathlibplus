import Mathlib

namespace MathlibPlus.Analysis.CayleyRate

/-- Claim 4640: the Cayley coordinate of a nonzero complex point has the
 displayed quotient form. -/
theorem cayleyCoordinate_formula (ρ : ℂ) (hρ : ρ ≠ 0) :
    1 - 1 / ρ = (ρ - 1) / ρ := by
  field_simp [hρ]

/-- Claim 14198: the positive-axis rate formula and its strict consequence.
 The source's ``strip point'' is represented by real coordinates `β, γ`, with
 the explicitly stated hypothesis `β < 1` and the nonzero-point hypothesis. -/
theorem exactPositiveAxisRateFormula (β γ : ℝ) (hβ : β < 1)
    (hρ : (β : ℂ) + (γ : ℂ) * Complex.I ≠ 0) :
    let ρ : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I
    let wρ : ℂ := 1 - 1 / ρ
    1 - Complex.re (1 / wρ) =
        1 - Complex.re (ρ / (ρ - 1)) ∧
      1 - Complex.re (ρ / (ρ - 1)) =
        (1 - β) / ((β - 1)^2 + γ^2) ∧
      0 < (1 - β) / ((β - 1)^2 + γ^2) ∧
      Complex.re (1 / wρ) < 1 := by
  dsimp
  have hρ1 : ((β : ℂ) + (γ : ℂ) * Complex.I) - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hCayley :
      1 / (1 - 1 / ((β : ℂ) + (γ : ℂ) * Complex.I)) =
        ((β : ℂ) + (γ : ℂ) * Complex.I) /
          (((β : ℂ) + (γ : ℂ) * Complex.I) - 1) := by
    field_simp [hρ, hρ1]
  have hden : (β - 1)^2 + γ^2 ≠ 0 := by
    intro h
    have hβ1 : β - 1 = 0 := by
      nlinarith [sq_nonneg (β - 1), sq_nonneg γ]
    linarith
  have hreal :
      1 - Complex.re
          (((β : ℂ) + (γ : ℂ) * Complex.I) /
            (((β : ℂ) + (γ : ℂ) * Complex.I) - 1)) =
        (1 - β) / ((β - 1)^2 + γ^2) := by
    simp [Complex.div_re, Complex.normSq_apply]
    field_simp [hden]
    ring
  have hpos : 0 < (1 - β) / ((β - 1)^2 + γ^2) := by
    have hden_pos : 0 < (β - 1)^2 + γ^2 := by
      have hden' : (β - 1)^2 + γ^2 ≠ 0 := hden
      positivity
    positivity
  refine ⟨?_, hreal, hpos, ?_⟩
  · rw [hCayley]
  · rw [hCayley]
    linarith [hreal, hpos]

end MathlibPlus.Analysis.CayleyRate
