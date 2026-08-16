import MathlibPlus.Basic

/-!
# Rational congruence and determinant sign

Formalization of admitted claim 392 from source record `C-0024`.  The determinant
identity is algebraic and does not use the Hankel structure of the real matrix family,
so it is proved for every such family.
-/

namespace MathlibPlus.LinearAlgebra.RationalCongruence

/-- Congruence by a fixed invertible rational matrix multiplies a real determinant by
the positive square of the rational determinant, and therefore preserves both strict
signs. -/
theorem det_congr {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (hP : P.det ≠ 0)
    (M : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix.det (P.map (algebraMap ℚ ℝ) * M t * (P.map (algebraMap ℚ ℝ)).transpose) =
      (P.det : ℝ) ^ 2 * Matrix.det (M t) ∧
    (0 < Matrix.det (P.map (algebraMap ℚ ℝ) * M t *
        (P.map (algebraMap ℚ ℝ)).transpose) ↔ 0 < Matrix.det (M t)) ∧
    (Matrix.det (P.map (algebraMap ℚ ℝ) * M t *
        (P.map (algebraMap ℚ ℝ)).transpose) < 0 ↔ Matrix.det (M t) < 0) := by
  have hcast : (P.det : ℝ) ≠ 0 := by exact_mod_cast hP
  have hsquare : 0 < (P.det : ℝ) ^ 2 := sq_pos_of_ne_zero hcast
  have hmap : Matrix.det (P.map (algebraMap ℚ ℝ)) = (P.det : ℝ) :=
    (RingHom.map_det (algebraMap ℚ ℝ) P).symm
  have hdet :
      Matrix.det (P.map (algebraMap ℚ ℝ) * M t *
          (P.map (algebraMap ℚ ℝ)).transpose) =
        (P.det : ℝ) ^ 2 * Matrix.det (M t) := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap]
    ring
  rw [hdet]
  refine ⟨rfl, mul_pos_iff_of_pos_left hsquare, ?_⟩
  rw [mul_neg_iff]
  have hnot : ¬ (P.det : ℝ) ^ 2 < 0 := not_lt_of_ge hsquare.le
  simp only [hsquare, true_and, hnot, false_and, or_false]

end MathlibPlus.LinearAlgebra.RationalCongruence
