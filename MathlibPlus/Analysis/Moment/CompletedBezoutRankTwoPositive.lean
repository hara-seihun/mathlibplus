import Mathlib

/-!
# The rank-two completed Bezout positive chamber

This is the exact algebraic rank-two specialization of the completed Bezout
matrix with factorial-scaled moments.
-/

namespace MathlibPlus.Analysis.Moment

/-- For factorial-scaled moments `h_j = m_j / (2j)!`, the rank-two completed
Bezout determinant is positive exactly on the affine chamber
`S + 5R > 10/3`, where `R = m₁²/(m₀m₂)` and `S = m₁m₃/m₂²`.

The displayed `2 × 2` matrix is the rank-two instance of
`Cᐟᴺᵢⱼ = ∑ₐ (i+j+1-2a) hₐ h_(i+j+1-a)`.
-/
theorem completedBezoutRankTwoPositiveIff
    (m : Fin 4 → ℝ) (hm₀ : 0 < m 0) (hm₂ : 0 < m 2) :
    let h : Fin 4 → ℝ := fun j => m j / (Nat.factorial (2 * (j : ℕ)) : ℕ)
    let C : Matrix (Fin 2) (Fin 2) ℝ :=
      !![h 0 * h 1, 2 * h 0 * h 2;
         2 * h 0 * h 2, 3 * h 0 * h 3 + h 1 * h 2]
    let R := (m 1) ^ 2 / (m 0 * m 2)
    let S := m 1 * m 3 / (m 2) ^ 2
    Matrix.det C > 0 ↔ S + 5 * R > 10 / 3 := by
  dsimp
  rw [Matrix.det_fin_two]
  norm_num [Nat.factorial]
  have hm₀ne : m 0 ≠ 0 := ne_of_gt hm₀
  have hm₂ne : m 2 ≠ 0 := ne_of_gt hm₂
  field_simp
  constructor <;> intro h <;> nlinarith

/-- Claim 12739: the two-atom rank-two completed-Bezout chamber identity.

Here `m j = 1 + w L^j` are the moments of `δ₁ + wδ_L`, and `C` is the
factorial-scaled rank-two completed Bezout matrix displayed above. -/
theorem twoAtomChamberIdentity (w L : ℝ) (hw : 0 < w) (hL : 0 < L) :
    let m : Fin 4 → ℝ := fun j => 1 + w * L ^ (j : ℕ)
    let h : Fin 4 → ℝ :=
      fun j => m j / (Nat.factorial (2 * (j : ℕ)) : ℕ)
    let C : Matrix (Fin 2) (Fin 2) ℝ :=
      !![h 0 * h 1, 2 * h 0 * h 2;
         2 * h 0 * h 2, 3 * h 0 * h 3 + h 1 * h 2]
    let R := (m 1) ^ 2 / (m 0 * m 2)
    let S := m 1 * m 3 / (m 2) ^ 2
    let Q := 3 * S + 15 * R - 10
    1440 * Matrix.det C = m 0 ^ 2 * m 2 ^ 2 * Q := by
  dsimp
  have hm0 : 0 < 1 + w * L ^ (0 : ℕ) := by positivity
  have hm2 : 0 < 1 + w * L ^ (2 : ℕ) := by positivity
  have hm0ne : 1 + w * L ^ (0 : ℕ) ≠ 0 := ne_of_gt hm0
  have hm2ne : 1 + w * L ^ (2 : ℕ) ≠ 0 := ne_of_gt hm2
  rw [Matrix.det_fin_two]
  norm_num [Nat.factorial]
  field_simp [hm0ne, hm2ne]
  ring

end MathlibPlus.Analysis.Moment
