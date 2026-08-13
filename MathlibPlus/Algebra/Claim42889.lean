import Mathlib

namespace MathlibPlus.Algebra.Claim42889

/-- The quadratic homogeneous determinant piece from admitted claim 42889. -/
noncomputable def determinantPiece₂ (t : Fin 4 → ℝ) : ℝ :=
  (48 * t 0 * t 2 - 12 * t 0 * t 3 - 64 * (t 1) ^ 2 +
      20 * t 1 * t 2 + 3 * t 1 * t 3 - 4 * (t 2) ^ 2) / 64

/-- The cubic homogeneous determinant piece from admitted claim 42889. -/
noncomputable def determinantPiece₃ (t : Fin 4 → ℝ) : ℝ :=
  (64 * (t 0) ^ 2 * t 1 - 64 * (t 0) ^ 2 * t 2 +
      12 * (t 0) ^ 2 * t 3 + 48 * t 0 * (t 1) ^ 2 -
      16 * t 0 * t 1 * t 2 - 6 * t 0 * t 1 * t 3 +
      8 * t 0 * (t 2) ^ 2 - (t 1) ^ 2 * t 2) / 128

/-- The quartic homogeneous determinant piece from admitted claim 42889. -/
noncomputable def determinantPiece₄ (t : Fin 4 → ℝ) : ℝ :=
  t 0 * (3 * t 0 * t 1 * t 3 - 4 * t 0 * (t 2) ^ 2 + (t 1) ^ 2 * t 2) / 256

/-- The complete determinant expression from admitted claim 42889. -/
noncomputable def determinantPieces (t : Fin 4 → ℝ) : ℝ :=
  determinantPiece₂ t + determinantPiece₃ t + determinantPiece₄ t

theorem determinantPiece₂_smul (r : ℝ) (t : Fin 4 → ℝ) :
    determinantPiece₂ (r • t) = r ^ 2 * determinantPiece₂ t := by
  simp [determinantPiece₂]
  ring

theorem determinantPiece₃_smul (r : ℝ) (t : Fin 4 → ℝ) :
    determinantPiece₃ (r • t) = r ^ 3 * determinantPiece₃ t := by
  simp [determinantPiece₃]
  ring

theorem determinantPiece₄_smul (r : ℝ) (t : Fin 4 → ℝ) :
    determinantPiece₄ (r • t) = r ^ 4 * determinantPiece₄ t := by
  simp [determinantPiece₄]
  ring

end MathlibPlus.Algebra.Claim42889
