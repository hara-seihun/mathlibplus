import Mathlib

namespace MathlibPlus.Algebra.Claim1649

/-- The displayed stable `S₃` base polynomial has positive coefficients and is
strictly positive on the nonnegative half-line.  The source-specific name
`S₃` is represented here by its displayed polynomial expression. -/
theorem stableS3BasePolynomial_claim1649 :
    ∀ (m : ℕ),
      (0 < (64 : ℝ)) ∧
      0 < 64 * ((2 * m : ℕ) + 9 : ℝ) ∧
      0 < 4 * ((27 * m ^ 2 + 241 * m + 526 : ℕ) : ℝ) ∧
      0 < 2 * ((3 * m + 16 : ℕ) : ℝ) * ((8 * m ^ 2 + 65 * m + 129 : ℕ) : ℝ) ∧
      0 < ((137 * m ^ 4 + 2498 * m ^ 3 + 16891 * m ^ 2 + 50242 * m + 55728 : ℕ) : ℝ) / 12 ∧
      0 < (((m + 4) * (m + 6) *
        (7 * m ^ 3 + 94 * m ^ 2 + 413 * m + 614 : ℕ) : ℕ) : ℝ) / 6 ∧
      ∀ b : ℝ, 0 ≤ b →
        0 < 64 * b ^ 5 +
          64 * ((2 * m : ℕ) + 9 : ℝ) * b ^ 4 +
          4 * ((27 * m ^ 2 + 241 * m + 526 : ℕ) : ℝ) * b ^ 3 +
          2 * ((3 * m + 16 : ℕ) : ℝ) *
            ((8 * m ^ 2 + 65 * m + 129 : ℕ) : ℝ) * b ^ 2 +
          ((137 * m ^ 4 + 2498 * m ^ 3 + 16891 * m ^ 2 + 50242 * m + 55728 : ℕ) : ℝ) * b / 12 +
          (((m + 4) * (m + 6) *
            (7 * m ^ 3 + 94 * m ^ 2 + 413 * m + 614 : ℕ) : ℕ) : ℝ) / 6 := by
  intro m
  constructor
  · norm_num
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  intro b hb
  positivity

end MathlibPlus.Algebra.Claim1649
