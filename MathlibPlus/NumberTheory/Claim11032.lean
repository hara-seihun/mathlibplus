import Mathlib

namespace MathlibPlus.NumberTheory.Claim11032

open Polynomial

/-- The explicit matrices in claim 11032 have different traces, so they cannot
be conjugate over `ℚ`.  The finite-field point count and the two characteristic
polynomials are included as exact certificates. -/
theorem ellipticFrobenius_conjugacy_mismatch_claim11032 :
    let F : Matrix (Fin 2) (Fin 2) ℚ := !![0, -5; 1, -3]
    let H : Matrix (Fin 2) (Fin 2) ℚ := !![5, 0; 0, 1 / 5]
    let E : Type := Option {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}
    Fintype.card E = 9 ∧
      Matrix.trace F = -3 ∧
      F.charpoly = X ^ 2 + Polynomial.C (3 : ℚ) * X + Polynomial.C 5 ∧
      (∀ u : Polynomial ℚ,
        Matrix.det (1 - u • Matrix.map F Polynomial.C) =
          Polynomial.C (1 : ℚ) + Polynomial.C 3 * u + Polynomial.C 5 * u ^ 2) ∧
      Matrix.trace H = 26 / 5 ∧
      (((Matrix.trace F : ℚ) : ℝ) / Real.sqrt 5 = (-3 : ℝ) / Real.sqrt 5) ∧
      Matrix.trace F ≠ Matrix.trace H ∧
      ¬ ∃ P : Matrix (Fin 2) (Fin 2) ℝ,
        IsUnit P ∧
          P * (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ =
            (!![5, 0; 0, (1 : ℝ) / 5] : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp
  have hcard : Fintype.card (Option {p : ZMod 5 × ZMod 5 // p.2 ^ 2 = p.1 ^ 3 + p.1 + 1}) = 9 := by
    decide
  have hFtrace : Matrix.trace (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) = -3 := by
    simp [Matrix.trace, Fin.sum_univ_two]
  have hFcharpoly :
      (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ).charpoly =
        X ^ 2 + Polynomial.C (3 : ℚ) * X + Polynomial.C 5 := by
    rw [Matrix.charpoly_fin_two, hFtrace, Matrix.det_fin_two]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hFdet : ∀ u : Polynomial ℚ,
      Matrix.det (1 - u • Matrix.map
        (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) Polynomial.C) =
        Polynomial.C (1 : ℚ) + Polynomial.C 3 * u + Polynomial.C 5 * u ^ 2 := by
    intro u
    rw [Matrix.det_fin_two]
    simp [Matrix.map, Matrix.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring_nf
  have hHtrace : Matrix.trace (!![5, 0; 0, 1 / 5] : Matrix (Fin 2) (Fin 2) ℚ) = 26 / 5 := by
    simp [Matrix.trace, Fin.sum_univ_two]
    norm_num
  have hnormalized :
      (((Matrix.trace (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℚ) : ℚ) : ℝ) /
        Real.sqrt 5 = (-3 : ℝ) / Real.sqrt 5) := by
    rw [hFtrace]
    norm_num
  refine ⟨hcard, hFtrace, hFcharpoly, hFdet, hHtrace, hnormalized, ?_, ?_⟩
  · rw [hFtrace, hHtrace]
    norm_num
  · rintro ⟨P, hP, hconj⟩
    have htrace :
        Matrix.trace (P * (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹) =
          Matrix.trace (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.trace_conj hP (!![0, -5; 1, -3] : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hconj] at htrace
    norm_num [Matrix.trace, Fin.sum_univ_two] at htrace

end MathlibPlus.NumberTheory.Claim11032
