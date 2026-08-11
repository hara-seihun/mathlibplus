import Mathlib

/-!
# Finite-divisor Toeplitz moment matrices

The finite divisor is represented, with multiplicity, by a map from a finite type
to nonzero complex points.  The definitions themselves make sense for any finite
complex family; the surrounding divisor application supplies nonvanishing and
inversion--conjugation stability.
-/

namespace MathlibPlus.LinearAlgebra.FiniteToeplitzMoment

open scoped BigOperators

/-- The Laurent monomial moment of a finite complex family. -/
noncomputable def finiteDivisorMoment {m : ℕ}
    (W : Fin m → ℂ) (exponent : ℤ) : ℂ :=
  ∑ r, W r ^ exponent

/-- The order-`N` Toeplitz moment matrix of a finite complex family:
its `(j,k)` entry is the moment of `u^(j-k)`. -/
noncomputable def finiteToeplitzMomentMatrix {m : ℕ}
    (W : Fin m → ℂ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun j k => finiteDivisorMoment W (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))

/-- Entrywise form of the finite Toeplitz moment matrix. -/
theorem finiteToeplitzMomentMatrix_apply {m : ℕ}
    (W : Fin m → ℂ) (N : ℕ) (j k : Fin (N + 1)) :
    finiteToeplitzMomentMatrix W N j k =
      ∑ r, W r ^ (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) := by
  rfl

end MathlibPlus.LinearAlgebra.FiniteToeplitzMoment
