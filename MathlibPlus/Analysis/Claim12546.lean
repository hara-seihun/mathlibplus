import Mathlib

open scoped BigOperators

namespace MathlibPlus.Analysis

private def h12546 (j : ℕ) : ℚ :=
  (1 + (17 / 16 : ℚ) / 4 ^ j) / (Nat.factorial (2 * j) : ℚ)

private def C12546 (N : ℕ) : Matrix (Fin N) (Fin N) ℚ := fun i j =>
  ∑ a ∈ Finset.range (min i.1 j.1 + 1),
    ((i.1 + j.1 + 1 - 2 * a : ℕ) : ℚ) * h12546 a *
      h12546 (i.1 + j.1 + 1 - a)

/-- Exact rank-four first-failure witness from the two-atom measure at
`ε = 17/16`.  The matrix sections are the literal completed sections
`C⁽ᴺ⁾ᵢⱼ = ∑ₐ (i+j+1-2a) hₐ hᵢ₊ⱼ₊₁₋ₐ`, with
`hⱼ = (1 + (17/16) 4⁻ʲ)/(2j)!`. -/
theorem rationalFirstFailureWitness_claim12546 :
    Matrix.det (C12546 1) = 2673 / 2048 ∧
      Matrix.det (C12546 2) = 4867731 / 335544320 ∧
      Matrix.det (C12546 3) = 41297737459 / 1724034232352768000 ∧
      Matrix.det (C12546 4) =
        -21732069816553 / 33164825631707303112395980800000 ∧
      0 < Matrix.det (C12546 1) ∧
      0 < Matrix.det (C12546 2) ∧
      0 < Matrix.det (C12546 3) ∧
      Matrix.det (C12546 4) < 0 := by
  native_decide

end MathlibPlus.Analysis
