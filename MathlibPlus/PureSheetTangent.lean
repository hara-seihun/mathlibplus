import Mathlib

/-!
# Pure-sheet tangent determinant

This file formalizes the exact algebraic anchor in Record 20 of legacy packet
`C-0036`.  It defines only the packet's explicit zero-activity tangent vector and
proves its determinant formula and positivity at three ordered knots.  No unresolved
folded-kernel or activity-locus assertion is introduced.
-/

namespace MathlibPlus.PureSheetTangent

/-- The explicit zero-reciprocal-activity tangent from packet `C-0036`. -/
noncomputable def pureSheetTangent (q l : ℝ) : Fin 3 → ℝ :=
  ![l⁻¹,
    (-7 * l + 4 * q) / (2 * l ^ 2),
    (151 * l ^ 2 - 216 * l * q + 48 * q ^ 2) / (16 * l ^ 3)]

/-- The three-row pure-sheet tangent determinant is a scaled Vandermonde product. -/
theorem pureSheetTangent_det (l x y z : ℝ) (hl : l ≠ 0) :
    Matrix.det (fun i j : Fin 3 => pureSheetTangent (![x, y, z] i) l j) =
      -6 * (x - y) * (x - z) * (y - z) / l ^ 6 := by
  change Matrix.det !![
    l⁻¹, (-7 * l + 4 * x) / (2 * l ^ 2),
      (151 * l ^ 2 - 216 * l * x + 48 * x ^ 2) / (16 * l ^ 3);
    l⁻¹, (-7 * l + 4 * y) / (2 * l ^ 2),
      (151 * l ^ 2 - 216 * l * y + 48 * y ^ 2) / (16 * l ^ 3);
    l⁻¹, (-7 * l + 4 * z) / (2 * l ^ 2),
      (151 * l ^ 2 - 216 * l * z + 48 * z ^ 2) / (16 * l ^ 3)] = _
  rw [Matrix.det_fin_three]
  simp
  field_simp [hl]
  ring

/-- At positive scale and strictly ordered knots, the pure-sheet tangent determinant
has the exact value and is strictly positive, as asserted in Record 20. -/
theorem pureSheetTangent_positive (l x y z : ℝ)
    (hl : 0 < l) (hxy : x < y) (hyz : y < z) :
    Matrix.det (fun i j : Fin 3 => pureSheetTangent (![x, y, z] i) l j) =
        -6 * (x - y) * (x - z) * (y - z) / l ^ 6 ∧
      0 < Matrix.det (fun i j : Fin 3 => pureSheetTangent (![x, y, z] i) l j) := by
  have hdet := pureSheetTangent_det l x y z (ne_of_gt hl)
  refine ⟨hdet, ?_⟩
  rw [hdet]
  have hxz : x < z := lt_trans hxy hyz
  have hxy' : x - y < 0 := sub_neg.mpr hxy
  have hxz' : x - z < 0 := sub_neg.mpr hxz
  have hyz' : y - z < 0 := sub_neg.mpr hyz
  have hp : 0 < (x - y) * (x - z) := mul_pos_of_neg_of_neg hxy' hxz'
  have hn : (x - y) * (x - z) * (y - z) < 0 := mul_neg_of_pos_of_neg hp hyz'
  apply div_pos
  · nlinarith
  · positivity

end MathlibPlus.PureSheetTangent
