import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 11446: the symmetric rational solutions of the displayed balanced
matrix equation are the stated one-dimensional family, with its determinant. -/
theorem claim11446_balanced_forms
    (a b c : ℚ)
    (h : Matrix.transpose (!![0, -9; 1, -7] : Matrix (Fin 2) (Fin 2) ℚ) *
          !![a, b; b, c] * !![0, -9; 1, -7] =
        9 • (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℚ)) :
    ∃ z : ℚ,
      (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℚ) =
        z • (!![(1 : ℚ) / 9, (-7 : ℚ) / 18;
               (-7 : ℚ) / 18, 1] : Matrix (Fin 2) (Fin 2) ℚ) ∧
      Matrix.det (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℚ) =
        -13 * z ^ 2 / 324 := by
  have h00 := congr_fun (congr_fun h 0) 0
  have h01 := congr_fun (congr_fun h 0) 1
  have h10 := congr_fun (congr_fun h 1) 0
  have h11 := congr_fun (congr_fun h 1) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  have hc : c = 9 * a := h00
  have hb : b = -(7 * a) / 2 := by
    linarith [h01, h00]
  refine ⟨9 * a, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rw [Matrix.det_fin_two]
    norm_num
    rw [hc, hb]
    ring

/-- Claim 24580, with the sign made explicit: after `P₂ = P₀ + P₁`,
`P₀'P₁ - P₀P₁' = P₀'P₂ - P₀P₂'`, while the third displayed
Wronskian has the opposite sign. -/
theorem claim24580_wronskian_identities
    {K : Type*} [CommRing K]
    (P₀ P₁ P₂ : Polynomial K) (h : P₀ + P₁ = P₂) :
    (P₀.derivative * P₁ - P₀ * P₁.derivative =
        P₀.derivative * P₂ - P₀ * P₂.derivative) ∧
      (P₀.derivative * P₁ - P₀ * P₁.derivative =
        -(P₁.derivative * P₂ - P₁ * P₂.derivative)) := by
  subst P₂
  simp only [Polynomial.derivative_add]
  constructor <;> ring

end MathlibPlus.Algebra
