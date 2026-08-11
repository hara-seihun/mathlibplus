import Mathlib

namespace MathlibPlus.Analysis.SingleSpike

noncomputable section

/-- The scale factor in the admitted single-spike family. Real powers are used
for the fractional exponents in the source formula. -/
def height (x : ℝ) (N : ℕ) : ℝ :=
  Real.exp (x / 2) * Real.sqrt (Nat.factorial N : ℝ) *
    x ^ (-(N : ℝ) / 2) * (N : ℝ) ^ (-(1 : ℝ) / 4)

/-- The coefficient sequence supported at the single index `N`. -/
def coefficient (x : ℝ) (N k : ℕ) : ℝ :=
  if k = N then height x N else 0

/-- The polynomial displayed in the admitted claim, over the complex numbers. -/
def polynomial (x : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  (height x N : ℂ) * z ^ N / (Nat.factorial N : ℂ)

theorem coefficient_eq_zero_of_ne {x : ℝ} {N k : ℕ} (h : k ≠ N) :
    coefficient x N k = 0 := by
  simp [coefficient, h]

theorem coefficient_at_index {x : ℝ} {N : ℕ} :
    coefficient x N N = height x N := by
  simp [coefficient]

theorem height_pos {x : ℝ} {N : ℕ} (hx : 0 < x) (hN : 1 ≤ N) :
    0 < height x N := by
  dsimp [height]
  positivity

end

end MathlibPlus.Analysis.SingleSpike
