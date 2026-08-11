import Mathlib

open scoped BigOperators

namespace MathlibPlus.MomentGeometry

private theorem twoAtomMomentMinor_pos
    (w L : ℝ) (hw : 0 < w) (hL : 1 < L) {j k : ℕ} (hjk : j < k) :
    0 <
      (1 / ((2 * j).factorial : ℝ)) *
          (w * L ^ k / ((2 * k).factorial : ℝ)) -
        (1 / ((2 * k).factorial : ℝ)) *
          (w * L ^ j / ((2 * j).factorial : ℝ)) := by
  rw [show
    (1 / ((2 * j).factorial : ℝ)) *
          (w * L ^ k / ((2 * k).factorial : ℝ)) -
        (1 / ((2 * k).factorial : ℝ)) *
          (w * L ^ j / ((2 * j).factorial : ℝ)) =
      w * (L ^ k - L ^ j) /
        (((2 * j).factorial : ℝ) * ((2 * k).factorial : ℝ)) by ring]
  exact div_pos
    (mul_pos hw (sub_pos.mpr (pow_lt_pow_right₀ hL hjk)))
    (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (Nat.cast_pos.mpr (Nat.factorial_pos _)))

/-- The two exact positive two-atom measures in C-0011 lie just below the two
one-sided sufficient thresholds while remaining outside the strict rank-two
chamber. Their two-row factorial-scaled moment tables have every available
(nonempty) minor strictly positive. -/
theorem nearThresholdCounterexamples :
    let mR : ℕ → ℝ := fun j => 1 + (437 / 500 : ℝ) * 10000 ^ j
    let mS : ℕ → ℝ := fun j => 1 + (429 / 10000000000 : ℝ) * 10000000 ^ j
    let R : (ℕ → ℝ) → ℝ := fun m => m 1 ^ 2 / (m 0 * m 2)
    let S : (ℕ → ℝ) → ℝ := fun m => m 1 * m 3 / m 2 ^ 2
    let strictlyTotallyPositiveTwoRowTable : ℝ → ℝ → Prop := fun w L =>
      (∀ j : ℕ,
        0 < 1 / ((2 * j).factorial : ℝ) ∧
        0 < w * L ^ j / ((2 * j).factorial : ℝ)) ∧
      (∀ ⦃j k : ℕ⦄, j < k →
        0 <
          (1 / ((2 * j).factorial : ℝ)) *
              (w * L ^ k / ((2 * k).factorial : ℝ)) -
            (1 / ((2 * k).factorial : ℝ)) *
              (w * L ^ j / ((2 * j).factorial : ℝ)))
    (4664 / 10000 : ℝ) < R mR ∧
      S mR + 5 * R mR ≤ 10 / 3 ∧
      (3329 / 1000 : ℝ) < S mS ∧
      S mS + 5 * R mS ≤ 10 / 3 ∧
      strictlyTotallyPositiveTwoRowTable (437 / 500) 10000 ∧
      strictlyTotallyPositiveTwoRowTable (429 / 10000000000) 10000000 := by
  dsimp only
  constructor
  · norm_num [pow_succ]
  constructor
  · norm_num [pow_succ]
  constructor
  · norm_num [pow_succ]
  constructor
  · norm_num [pow_succ]
  constructor
  · constructor
    · intro j
      constructor <;> positivity
    · intro j k hjk
      exact twoAtomMomentMinor_pos (437 / 500) 10000 (by norm_num) (by norm_num) hjk
  · constructor
    · intro j
      constructor <;> positivity
    · intro j k hjk
      exact twoAtomMomentMinor_pos (429 / 10000000000) 10000000
        (by norm_num) (by norm_num) hjk

end MathlibPlus.MomentGeometry
