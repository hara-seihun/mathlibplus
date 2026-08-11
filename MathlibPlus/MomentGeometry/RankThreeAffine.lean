import Mathlib

open scoped BigOperators

namespace MathlibPlus.MomentGeometry

/-- The completed rank-three Bezout determinant, after removing mass and support scale,
is affine in the highest consecutive moment ratio. -/
theorem exactAffineRankThreeDeterminantFormula (m : ℕ → ℝ)
    (hm : ∀ j ≤ 5, 0 < m j) :
    let h : ℕ → ℝ := fun j => m j / Nat.factorial (2 * j)
    let C3 : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
      ∑ x ∈ Finset.range (min i.1 j.1 + 1),
        (i.1 + j.1 + 1 - 2 * x : ℕ) * h x * h (i.1 + j.1 + 1 - x)
    let ρ1 := m 0 * m 2 / m 1 ^ 2
    let ρ2 := m 1 * m 3 / m 2 ^ 2
    let ρ3 := m 2 * m 4 / m 3 ^ 2
    let ρ4 := m 3 * m 5 / m 4 ^ 2
    let a := 3 * ρ1 * ρ2 - 10 * ρ1 + 15
    let correction :=
      -180 * ρ1 ^ 2 * ρ2 ^ 3 * ρ3 ^ 2 +
      2520 * ρ1 ^ 2 * ρ2 ^ 2 * ρ3 -
      2646 * ρ1 ^ 2 * ρ2 ^ 2 -
      2205 * ρ1 * ρ2 ^ 2 * ρ3 -
      9450 * ρ1 * ρ2 * ρ3 +
      26460 * ρ1 * ρ2 - 14700 * ρ1 +
      14175 * ρ2 * ρ3 - 35280 * ρ2 + 22050
    36578304000 * C3.det =
      (m 1 ^ 9 / m 0 ^ 3) * ρ1 ^ 4 * ρ2 *
        (35 * ρ1 * ρ2 ^ 2 * ρ3 ^ 2 * a * ρ4 + correction) := by
  dsimp
  have hm0 : m 0 ≠ 0 := ne_of_gt (hm 0 (by omega))
  have hm1 : m 1 ≠ 0 := ne_of_gt (hm 1 (by omega))
  have hm2 : m 2 ≠ 0 := ne_of_gt (hm 2 (by omega))
  have hm3 : m 3 ≠ 0 := ne_of_gt (hm 3 (by omega))
  have hm4 : m 4 ≠ 0 := ne_of_gt (hm 4 (by omega))
  have hmatrix :
      (fun i j : Fin 3 =>
        ∑ x ∈ Finset.range (min i.1 j.1 + 1),
          (i.1 + j.1 + 1 - 2 * x : ℕ) *
            (m x / Nat.factorial (2 * x)) *
            (m (i.1 + j.1 + 1 - x) /
              Nat.factorial (2 * (i.1 + j.1 + 1 - x)))) =
        (!![m 0 * m 1 / 2, m 0 * m 2 / 12, m 0 * m 3 / 240;
            m 0 * m 2 / 12, m 0 * m 3 / 240 + m 1 * m 2 / 48,
              m 0 * m 4 / 10080 + m 1 * m 3 / 720;
            m 0 * m 3 / 240, m 0 * m 4 / 10080 + m 1 * m 3 / 720,
              m 0 * m 5 / 725760 + m 1 * m 4 / 26880 + m 2 * m 3 / 17280] :
          Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Finset.sum_range_succ]
    <;> ring
  rw [hmatrix, Matrix.det_fin_three]
  simp (discharger := decide) [Matrix.cons_val']
  field_simp
  ring

end MathlibPlus.MomentGeometry
