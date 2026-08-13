import Mathlib

namespace MathlibPlus.Algebra.Claim10472

open Matrix

/-- Exact trace-square identity for the two coupled local blocks. -/
theorem trace_square_claim10472 {R : Type*} [CommRing R] (x c y : R) :
    (let A : Matrix (Fin 2) (Fin 2) R := !![x, c * x; c * y, y]
     Matrix.trace (A * A) = x ^ 2 + y ^ 2 + 2 * c ^ 2 * x * y) := by
  dsimp
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- At zero coupling the mixed term disappears. -/
theorem trace_square_decoupled_claim10472 {R : Type*} [CommRing R] (x y : R) :
    (let A : Matrix (Fin 2) (Fin 2) R := !![x, 0; 0, y]
     Matrix.trace (A * A) = x ^ 2 + y ^ 2) := by
  dsimp
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- Over the rational coefficient field, a nonzero coupling between two
nonzero local weights contributes a nonzero mixed term. -/
theorem mixed_term_nonzero_claim10472 {x c y : ℚ}
    (hx : x ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0) :
    2 * c ^ 2 * x * y ≠ 0 := by
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hc)) hx) hy

end MathlibPlus.Algebra.Claim10472
