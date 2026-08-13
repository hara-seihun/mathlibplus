import Mathlib

namespace MathlibPlus.Algebra.Claim2871

/-- The rank-two signed crossing determinant for the displayed bidiagonal
factorization.  The sign matrix `D` is `diag (1, -1)`, the convention
consistent with the source's displayed formula. -/
theorem crossingFormula_claim2871
    (ell u d₁ d₂ : ℝ)
    (_hell : 0 < ell) (_hu : 0 < u) (_hd₁ : 0 < d₁) (_hd₂ : 0 < d₂) :
    let B : Matrix (Fin 2) (Fin 2) ℝ :=
      !![1, 0; ell, 1] * !![d₁, 0; 0, d₂] * !![1, u; 0, 1]
    let D : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    Matrix.det (1 + D * B) = (1 + d₁) * (1 - d₂) - ell * u * d₁ := by
  dsimp
  have hB :
      (!![1, 0; ell, 1] : Matrix (Fin 2) (Fin 2) ℝ) *
          !![d₁, 0; 0, d₂] * !![1, u; 0, 1] =
        !![d₁, d₁ * u; ell * d₁, ell * d₁ * u + d₂] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hB]
  rw [Matrix.det_fin_two]
  simp [Matrix.one_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Positive bidiagonal parameters do not impose any upper bound on `ell * u`. -/
theorem crossingProductUnbounded_claim2871 :
    ∀ C : ℝ, 0 < C → ∃ ell u : ℝ, 0 < ell ∧ 0 < u ∧ C < ell * u := by
  intro C hC
  refine ⟨C + 1, 1, by linarith, zero_lt_one, ?_⟩
  nlinarith

end MathlibPlus.Algebra.Claim2871
