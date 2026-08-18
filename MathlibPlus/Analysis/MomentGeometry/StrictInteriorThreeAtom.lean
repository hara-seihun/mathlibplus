import Mathlib

namespace MathlibPlus.Analysis.MomentGeometry

noncomputable section

open scoped BigOperators

/-- Claim 373: the displayed strict-interior three-atom moment vector has
positive moment data and rank-two slack, while the normalized rank-three
 determinant and the fourth-ratio wall gap are negative. -/
def strictInteriorThreeAtomCounterexample : Prop :=
  let m : ℕ → ℝ := fun j =>
    10 * (1 : ℝ) ^ j + (2 : ℝ) ^ j + 2 * (7 : ℝ) ^ j
  let h : ℕ → ℝ := fun j => m j / (Nat.factorial (2 * j) : ℝ)
  let completedBezout : (N : ℕ) → Matrix (Fin N) (Fin N) ℝ := fun _ =>
    Matrix.of fun i j =>
      ∑ k ∈ Finset.range (min i.1 j.1 + 1),
        ((i.1 + j.1 + 1 - 2 * k : ℕ) : ℝ) * h k *
          h (i.1 + j.1 + 1 - k)
  let ρ : ℕ → ℝ := fun j =>
    m (j - 1) * m (j + 1) / m j ^ 2
  let a : ℝ := 3 * ρ 1 * ρ 2 - 10 * ρ 1 + 15
  let wallConstant : ℝ :=
    -180 * ρ 1 ^ 2 * ρ 2 ^ 3 * ρ 3 ^ 2 +
      2520 * ρ 1 ^ 2 * ρ 2 ^ 2 * ρ 3 -
      2646 * ρ 1 ^ 2 * ρ 2 ^ 2 -
      2205 * ρ 1 * ρ 2 ^ 2 * ρ 3 -
      9450 * ρ 1 * ρ 2 * ρ 3 +
      26460 * ρ 1 * ρ 2 - 14700 * ρ 1 +
      14175 * ρ 2 * ρ 3 - 35280 * ρ 2 + 22050
  let ρ4Star : ℝ :=
    -wallConstant / (35 * ρ 1 * ρ 2 ^ 2 * ρ 3 ^ 2 * a)
  m 0 = 13 ∧ m 1 = 26 ∧ m 2 = 112 ∧ m 3 = 704 ∧
    m 4 = 4828 ∧ m 5 = 33656 ∧
    (∀ j : ℕ, 0 < m j) ∧
    m 0 * m 2 / m 1 ^ 2 = 28 / 13 ∧
    (15 / 7 : ℝ) < m 0 * m 2 / m 1 ^ 2 ∧
    m 3 * m 5 - m 4 ^ 2 = 384240 ∧
    0 < m 3 * m 5 - m 4 ^ 2 ∧
    3 * m 0 * m 1 * m 3 + 15 * m 1 ^ 2 * m 2 -
        10 * m 0 * m 2 ^ 2 = 218816 ∧
    0 < Matrix.det (completedBezout 2) ∧
    36578304000 * Matrix.det (completedBezout 3) = -23793618030208 ∧
    ρ 4 - ρ4Star < -(55 / 100 : ℝ)

end

end MathlibPlus.Analysis.MomentGeometry
