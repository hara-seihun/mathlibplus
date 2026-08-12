import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim7682

noncomputable section

/-- The one-negative-square identity in claim 7682 (source K-0026, Eq. 5.1).
The inverse scale is taken in `ℂ`, matching the complexified moment form. -/
private lemma crossTerm (ρ : ℝ) (hρ : 0 < ρ) (M₀ M₂ : ℂ) :
    Complex.re (((ρ : ℂ) * M₀) * star ((ρ : ℂ)⁻¹ * M₂)) =
      Complex.re (M₂ * star M₀) := by
  rw [star_mul]
  have hs : star (ρ : ℂ) = (ρ : ℂ) := by simp
  rw [star_inv₀, hs, ← Complex.ofReal_inv]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp
  have hM₂re : (star M₂).re = M₂.re := rfl
  have hM₂im : (star M₂).im = -M₂.im := rfl
  have hM₀re : (star M₀).re = M₀.re := rfl
  have hM₀im : (star M₀).im = -M₀.im := rfl
  rw [hM₂re, hM₂im, hM₀re, hM₀im]
  ring

/--
The identity
`Re (M₂ * conj M₀) = (‖ρ M₀ + ρ⁻¹ M₂‖² - ‖ρ M₀ - ρ⁻¹ M₂‖²) / 4`
for every positive real scale and complex moments.
-/
theorem claim7682_oneNegativeSquare (ρ : ℝ) (hρ : 0 < ρ) (M₀ M₂ : ℂ) :
    Complex.re (M₂ * star M₀) =
      (Complex.normSq ((ρ : ℂ) * M₀ + (ρ : ℂ)⁻¹ * M₂) -
        Complex.normSq ((ρ : ℂ) * M₀ - (ρ : ℂ)⁻¹ * M₂)) / 4 := by
  rw [Complex.normSq_add, Complex.normSq_sub]
  have hcross :
      ((ρ : ℂ) * M₀ * (starRingEnd ℂ) ((ρ : ℂ)⁻¹ * M₂)).re =
        Complex.re (M₂ * star M₀) := by
    simpa only [starRingEnd_apply] using crossTerm ρ hρ M₀ M₂
  rw [show (↑ρ * M₀ * (starRingEnd ℂ) ((↑ρ)⁻¹ * M₂)).re = _ from hcross]
  ring

/-- The split-curvature nonnegativity is equivalent to the two-positive-square
 domination of the negative channel. -/
theorem claim7682_splitCurvatureIff (ρ : ℝ) (hρ : 0 < ρ)
    (M₀ M₁ M₂ : ℂ) :
    0 ≤ Complex.normSq M₁ + Complex.re (M₂ * star M₀) ↔
      Complex.normSq ((ρ : ℂ) * M₀ - (ρ : ℂ)⁻¹ * M₂) ≤
        4 * Complex.normSq M₁ +
          Complex.normSq ((ρ : ℂ) * M₀ + (ρ : ℂ)⁻¹ * M₂) := by
  have hsq := claim7682_oneNegativeSquare ρ hρ M₀ M₂
  rw [hsq]
  constructor <;> intro h <;> linarith

/-- The matrix realization of the three complex channels, with entrywise
conjugation, has the split invariant as half its trace. -/
theorem claim7682_traceRealization (M₀ M₁ M₂ : ℂ) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![M₁, M₀; M₂, -M₁]
    let Xbar : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(starRingEnd ℂ) M₁, (starRingEnd ℂ) M₀;
        (starRingEnd ℂ) M₂, (starRingEnd ℂ) (-M₁)]
    Complex.ofReal (Complex.normSq M₁ + Complex.re (M₂ * star M₀)) =
      Complex.ofReal (1 / 2) * Matrix.trace (X * Xbar) := by
  dsimp
  rw [Matrix.trace, Fin.sum_univ_two]
  have h0 :
      ((!![M₁, M₀; M₂, -M₁] : Matrix (Fin 2) (Fin 2) ℂ) *
          !![(starRingEnd ℂ) M₁, (starRingEnd ℂ) M₀;
            (starRingEnd ℂ) M₂, (starRingEnd ℂ) (-M₁)]).diag 0 =
        M₁ * star M₁ + M₀ * star M₂ := by
    simp [Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 :
      ((!![M₁, M₀; M₂, -M₁] : Matrix (Fin 2) (Fin 2) ℂ) *
          !![(starRingEnd ℂ) M₁, (starRingEnd ℂ) M₀;
            (starRingEnd ℂ) M₂, (starRingEnd ℂ) (-M₁)]).diag 1 =
        M₂ * star M₀ + (-M₁) * star (-M₁) := by
    simp [Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h0, h1]
  apply Complex.ext
  · simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  · simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring

/-- For `ρ > 0`, the split-Cartan matrix with diagonal entries
`√ρ` and `(√ρ)⁻¹` sends the two root channels to weights `ρ` and `ρ⁻¹`.
The inverse matrix is written explicitly and the action is the source's
`a_ρ X a_ρ⁻¹`. -/
theorem claim7682_splitCartanAction (ρ : ℝ) (hρ : 0 < ρ) (M₀ M₁ M₂ : ℂ) :
    let X : Matrix (Fin 2) (Fin 2) ℂ := !![M₁, M₀; M₂, -M₁]
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(Real.sqrt ρ : ℂ), 0; 0, (Real.sqrt ρ : ℂ)⁻¹]
    let Ainv : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(Real.sqrt ρ : ℂ)⁻¹, 0; 0, (Real.sqrt ρ : ℂ)]
    A * X * Ainv =
      !![M₁, (ρ : ℂ) * M₀; (ρ : ℂ)⁻¹ * M₂, -M₁] := by
  dsimp
  have haction (r : ℂ) (hr : r ≠ 0) :
      (!![r, 0; 0, r⁻¹] : Matrix (Fin 2) (Fin 2) ℂ) *
          !![M₁, M₀; M₂, -M₁] *
          !![r⁻¹, 0; 0, r] =
        !![M₁, r ^ 2 * M₀; r⁻¹ ^ 2 * M₂, -M₁] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;> ring
  rw [haction]
  · have hs : (Real.sqrt ρ : ℂ) ^ 2 = (ρ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hρ)]
    have hsinv : (Real.sqrt ρ : ℂ)⁻¹ ^ 2 = (ρ : ℂ)⁻¹ := by
      calc
        (Real.sqrt ρ : ℂ)⁻¹ ^ 2 = ((Real.sqrt ρ : ℂ) ^ 2)⁻¹ := by rw [inv_pow]
        _ = (ρ : ℂ)⁻¹ := by rw [hs]
    rw [hs, hsinv]
  · exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hρ)

end
end MathlibPlus.LinearAlgebra.Claim7682
