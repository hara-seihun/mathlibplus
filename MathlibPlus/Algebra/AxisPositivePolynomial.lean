import Mathlib

open Polynomial

namespace MathlibPlus.Algebra

/-!
# Axis-positive even polynomial family

This is the exact algebraic content of admitted claim 9654.  The polynomial is
kept over `ℤ` to make its integer coefficients explicit; its real and complex
evaluations state the two axis claims.
-/

/-- Claim 9654: for every `m ≥ 1`, `1 + X ^ (4 * m)` is even and is strictly
positive on both coordinate axes after evaluation. -/
theorem axisPositivePolynomial_family (m : ℕ) (_hm : 1 ≤ m) :
    let Q : Polynomial ℤ := 1 + X ^ (4 * m)
    (∀ z : ℂ, eval₂ (Int.castRingHom ℂ) (-z) Q =
        eval₂ (Int.castRingHom ℂ) z Q) ∧
      (∀ x : ℝ,
        eval₂ (Int.castRingHom ℝ) x Q = 1 + x ^ (4 * m) ∧
          0 < 1 + x ^ (4 * m)) ∧
      (∀ t : ℝ,
        eval₂ (Int.castRingHom ℂ) (Complex.I * t) Q =
            (1 + t ^ (4 * m) : ℂ) ∧
          0 < 1 + t ^ (4 * m)) := by
  dsimp
  constructor
  · intro z
    rw [show (1 + X ^ (4 * m) : Polynomial ℤ) = C 1 + X ^ (4 * m) by simp]
    rw [eval₂_add, eval₂_C, eval₂_pow, eval₂_X]
    rw [eval₂_add, eval₂_C, eval₂_pow, eval₂_X]
    have he : Even (4 * m) := by
      refine ⟨2 * m, ?_⟩
      omega
    rw [he.neg_pow]
  · constructor
    · intro x
      constructor
      · simp
      · have h : 0 ≤ x ^ (4 * m) := by
          rw [show 4 * m = (2 * m) * 2 by ring, pow_mul]
          exact sq_nonneg _
        linarith
    · intro t
      constructor
      · simp
        rw [mul_pow]
        have hi : Complex.I ^ (4 * m) = 1 := by
          rw [pow_mul]
          norm_num [Complex.I_sq]
        rw [hi]
        simp
      · have h : 0 ≤ t ^ (4 * m) := by
          rw [show 4 * m = (2 * m) * 2 by ring, pow_mul]
          exact sq_nonneg _
        linarith

end MathlibPlus.Algebra
