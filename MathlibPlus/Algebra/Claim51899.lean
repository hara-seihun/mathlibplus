import Mathlib

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim51899

/-- The coefficient `c_i = (A - i - 2) 2^i` from claim 51899. -/
def c (A i : ℕ) : ℕ := (A - i - 2) * 2 ^ i

/-- Substitution of the finite code `A = n + m + 2`, together with positivity
for every natural index `i < m`. -/
theorem c_finite_code {n m i : ℕ} (hi : i < m) :
    c (n + m + 2) i = (n + m - i) * 2 ^ i ∧
      0 < c (n + m + 2) i := by
  have hsub : n + m + 2 - i - 2 = n + m - i := by omega
  constructor
  · simp [c, hsub]
  · rw [c, hsub]
    exact Nat.mul_pos (by omega) (by positivity)

/-- Positive coefficients alone do not force all intermediate subset sums:
`1` and `3` are positive but no subset has sum `2`. -/
theorem positive_weights_need_not_cover_interval :
    let w : Fin 2 → ℕ := ![1, 3]
    (0 < w 0 ∧ 0 < w 1) ∧
      ¬ ∃ S : Finset (Fin 2), ∑ i ∈ S, w i = 2 := by
  dsimp
  constructor
  · norm_num
  · decide

end MathlibPlus.Algebra.Claim51899
