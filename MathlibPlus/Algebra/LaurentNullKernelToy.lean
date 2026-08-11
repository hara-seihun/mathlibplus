import Mathlib

open scoped LaurentPolynomial

namespace MathlibPlus.Algebra.LaurentNullKernelToy

/-- The toy's semantic relation vanishes at `q = -4/5` but is not a Laurent
multiple of the explicitly imposed reciprocal relation. -/
theorem semantic_relation_outside_formal_ideal :
    let q : ℚ[T;T⁻¹] := LaurentPolynomial.T 1
    let r : ℚ[T;T⁻¹] := 5 * q + 4
    let p : ℚ[T;T⁻¹] := (5 * q + 4) * (4 * q + 5) * (2 * q + 1) * (q + 2)
    let u₄₅ : ℚˣ := Units.mk0 (-4 / 5 : ℚ) (by norm_num)
    let u₅₄ : ℚˣ := Units.mk0 (-5 / 4 : ℚ) (by norm_num)
    LaurentPolynomial.eval₂ (RingHom.id ℚ) u₄₅ r = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) u₅₄ p = 0 ∧
      LaurentPolynomial.eval₂ (RingHom.id ℚ) u₅₄ r ≠ 0 ∧
      ¬ ∃ a : ℚ[T;T⁻¹], r = a * p := by
  dsimp
  constructor
  · simp only [map_add, map_mul, map_ofNat, LaurentPolynomial.eval₂_T]
    norm_num
  constructor
  · simp only [map_add, map_mul, map_ofNat, LaurentPolynomial.eval₂_T]
    norm_num
  constructor
  · simp only [map_add, map_mul, map_ofNat, LaurentPolynomial.eval₂_T]
    norm_num
  · intro h
    rcases h with ⟨a, ha⟩
    have heval := congrArg
      (LaurentPolynomial.eval₂ (RingHom.id ℚ)
        (Units.mk0 (-5 / 4 : ℚ) (by norm_num))) ha
    simp only [map_add, map_mul, map_ofNat, LaurentPolynomial.eval₂_T] at heval
    norm_num at heval

end MathlibPlus.Algebra.LaurentNullKernelToy
