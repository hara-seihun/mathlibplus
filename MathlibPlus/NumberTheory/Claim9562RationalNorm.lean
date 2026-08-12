import Mathlib

namespace MathlibPlus.NumberTheory.Claim9562RationalNorm

/-- Claim 9562: the rational norm form `x^2 + 3*x*y + y^2` is anisotropic. -/
theorem rationalNorm_anisotropic {x y : ℚ}
    (hxy : x ^ 2 + 3 * x * y + y ^ 2 = 0) :
    x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy
    have hratio : ((2 * x + 3 * y) / y) ^ 2 = (5 : ℚ) := by
      field_simp [hy]
      nlinarith [hxy]
    have hsquare : IsSquare (5 : ℚ) := by
      apply (isSquare_iff_exists_mul_self (5 : ℚ)).2
      refine ⟨(2 * x + 3 * y) / y, ?_⟩
      simpa [pow_two] using hratio.symm
    have hnot : ¬ IsSquare (5 : ℚ) := by
      intro hs
      apply Nat.prime_five.not_isSquare
      exact (Rat.isSquare_natCast_iff (n := 5)).mp (by simpa using hs)
    exact hnot hsquare
  subst y
  constructor
  · nlinarith [hxy]
  · rfl

end MathlibPlus.NumberTheory.Claim9562RationalNorm
