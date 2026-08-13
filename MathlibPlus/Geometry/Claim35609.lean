import Mathlib

namespace MathlibPlus.Geometry.Claim35609

/-- Exact coordinates, turns, and chord-length certificate for claim 35609's
repaired convex equilateral unit hexagon. -/
theorem repairedConvexEquilateralUnitHexagon :
    let s : ℝ := Real.sqrt 2
    let a : ℝ := s⁻¹
    let p0 : ℝ × ℝ := (0, 0)
    let p1 : ℝ × ℝ := (1, 0)
    let p2 : ℝ × ℝ := (1, 1)
    let p3 : ℝ × ℝ := (1 - a, 1 + a)
    let p4 : ℝ × ℝ := (-a, 1 + a)
    let p5 : ℝ × ℝ := (-a, a)
    let d (x y : ℝ × ℝ) : ℝ :=
      (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2
    let turn (x y : ℝ × ℝ) : ℝ := x.1 * y.2 - x.2 * y.1
    s ^ 2 = 2 ∧
    0 < s ∧
    -- The six consecutive sides have unit squared length.
    (d p0 p1 = 1 ∧ d p1 p2 = 1 ∧ d p2 p3 = 1 ∧
      d p3 p4 = 1 ∧ d p4 p5 = 1 ∧ d p5 p0 = 1) ∧
    -- The six successive turns are positive, so this order is strictly convex.
    (turn (p5 - p4) (p0 - p5) > 0 ∧
      turn (p0 - p5) (p1 - p0) > 0 ∧
      turn (p1 - p0) (p2 - p1) > 0 ∧
      turn (p2 - p1) (p3 - p2) > 0 ∧
      turn (p3 - p2) (p4 - p3) > 0 ∧
      turn (p4 - p3) (p5 - p4) > 0) ∧
    -- These are all nine non-side pairs, in increasing first index.
    (d p0 p2 = 2 ∧ d p0 p3 = 3 ∧ d p0 p4 = 2 + s ∧
      d p1 p3 = 2 + s ∧ d p1 p4 = 3 + 2 * s ∧ d p1 p5 = 2 + s ∧
      d p2 p4 = 2 + s ∧ d p2 p5 = 3 ∧ d p3 p5 = 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsinv : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, hs]
    norm_num
  have hsne : Real.sqrt 2 ≠ 0 := ne_of_gt hspos
  have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp [hsne]
    nlinarith [hs]
  repeat' first | constructor
  all_goals try dsimp
  all_goals try { exact hs }
  all_goals try { exact hspos }
  all_goals try { norm_num [hsinv, hinv, hsne] }
  all_goals try { field_simp [hsne] <;> ring_nf }
  all_goals try { nlinarith [hs, hspos] }
  all_goals ring

end MathlibPlus.Geometry.Claim35609
