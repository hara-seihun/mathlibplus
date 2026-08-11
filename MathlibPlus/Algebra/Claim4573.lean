import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim4573

/-- In an integral-domain coefficient ring, exact Euler locality forbids a
nonzero two-way coupling product. -/
theorem eulerLocality_triangular_claim4573
    {R : Type*} [CommRing R] [NoZeroDivisors R]
    (a b : R) (hlocal : a * b = 0) :
    a = 0 ∨ b = 0 := by
  exact eq_zero_or_eq_zero_of_mul_eq_zero hlocal

end MathlibPlus.Algebra.Claim4573
