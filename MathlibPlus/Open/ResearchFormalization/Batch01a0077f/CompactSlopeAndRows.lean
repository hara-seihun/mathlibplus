import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch01a0077f

/--
The real-part factorization and the exact same-sign/opposite-sign slope
classification of the root-cone margin.
-/
def claim12157_compactDangerousSlopeWindow : Prop :=
  (∀ x y : ℝ,
      x ^ 2 + 6 * x * y + y ^ 2 =
        (x + (3 + 2 * Real.sqrt 2) * y) *
          (x + (3 - 2 * Real.sqrt 2) * y)) ∧
  (∀ x y a b : ℝ,
      0 ≤ x * y →
        0 ≤ (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2) ∧
  (∀ x y : ℝ,
      x * y < 0 →
        ((abs (x / y) ≤ 3 - 2 * Real.sqrt 2 ∨
            3 + 2 * Real.sqrt 2 ≤ abs (x / y)) →
          ∀ a b : ℝ,
            0 ≤ (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2) ∧
        ((3 - 2 * Real.sqrt 2 < abs (x / y) ∧
            abs (x / y) < 3 + 2 * Real.sqrt 2) →
          x ^ 2 + 6 * x * y + y ^ 2 < 0 ∧
          ∀ a b : ℝ,
            (0 ≤ (a - b) ^ 2 + x ^ 2 + 6 * x * y + y ^ 2 ↔
              -(x ^ 2 + 6 * x * y + y ^ 2) ≤ (a - b) ^ 2)))

/--
An unequal weighted average of two sign rows separates exactly the ordered
row-pair fibers.
-/
def claim60240_unequalTwoRowLawJointFibers : Prop :=
  ∀ (C : Type) (T U : C → ℝ) (p : ℝ),
    ((∀ O : C, T O = (-1 : ℝ) ∨ T O = 1) ∧
      (∀ O : C, U O = (-1 : ℝ) ∨ U O = 1) ∧
      0 < p ∧ p < 1 ∧ p ≠ (1 / 2 : ℝ)) →
      ∀ O O' : C,
        (p * T O + (1 - p) * U O =
            p * T O' + (1 - p) * U O') ↔
          (T O = T O' ∧ U O = U O')

end MathlibPlus.Open.ResearchFormalization.Batch01a0077f
