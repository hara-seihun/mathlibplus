import Mathlib

namespace MathlibPlus.Algebra.Claim26906

/-- In a pure linear factor, reducing another linear factor modulo the fixed
factor leaves exactly the difference of their constant terms. -/
theorem linear_factor_mod_difference
    {R : Type*} [CommRing R] (aF aG : R) :
    (Polynomial.X + Polynomial.C aG) %ₘ (Polynomial.X + Polynomial.C aF) =
      Polynomial.C (aG - aF) := by
  have hF : Polynomial.X + Polynomial.C aF =
      Polynomial.X - Polynomial.C (-aF) := by simp
  rw [hF, Polynomial.modByMonic_X_sub_C_eq_C_eval]
  simp [sub_eq_add_neg, add_comm]

/-- The literal difference of the two pure linear factors is the same constant
polynomial. -/
theorem linear_factor_difference
    {R : Type*} [CommRing R] (aF aG : R) :
    (Polynomial.X + Polynomial.C aG) - (Polynomial.X + Polynomial.C aF) =
      Polynomial.C (aG - aF) := by
  simp only [sub_eq_add_neg, map_add, map_neg]
  abel

end MathlibPlus.Algebra.Claim26906
