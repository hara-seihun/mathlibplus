import Mathlib

namespace MathlibPlus.Analysis.Claim18492

/-- The two associated walls, represented as a pair of real-valued functions. -/
noncomputable def canonicalWalls (K : ℝ → ℝ) :
    (ℝ → ℝ) × (ℝ → ℝ) :=
  (fun s => s, fun s => s * K (s ^ 2))

/-- The first wall is the identity function. -/
theorem canonicalWalls_fst (K : ℝ → ℝ) (s : ℝ) :
    (canonicalWalls K).1 s = s := by
  rfl

/-- The second wall has the displayed `s K(s²)` form. -/
theorem canonicalWalls_snd (K : ℝ → ℝ) (s : ℝ) :
    (canonicalWalls K).2 s = s * K (s ^ 2) := by
  rfl

end MathlibPlus.Analysis.Claim18492
