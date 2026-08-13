import Mathlib

namespace MathlibPlus.Algebra

/--
The displayed normalized northeast entry from admitted claim 19538.  The
source's substitution is `w = X₁ + u`; the formal content retained here is
the exact polynomial in the normalized variable and its coefficient/sign
certificate.
-/
theorem northeastEntry_mixedSigns_claim19538 :
    let b : Polynomial ℤ :=
      592 - 5440 * Polynomial.X - 2304 * Polynomial.X ^ 2 +
        1024 * Polynomial.X ^ 3
    b.coeff 0 = 592 ∧
    b.coeff 1 = -5440 ∧
    b.coeff 2 = -2304 ∧
    b.coeff 3 = 1024 ∧
    (∃ n : ℕ, b.coeff n < 0) ∧
    ¬ (∀ n : ℕ, 0 ≤ b.coeff n) := by
  dsimp
  constructor
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
  constructor
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
  constructor
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
  constructor
  · norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
  constructor
  · refine ⟨1, ?_⟩
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
  · intro h
    have h1 := h 1
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_mul, Polynomial.coeff_X, Polynomial.coeff_X_pow,
      Polynomial.coeff_C] at h1

end MathlibPlus.Algebra
