import Mathlib.NumberTheory.FLT.MasonStothers

open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain EuclideanDomain

namespace MathlibPlus.NumberTheory.Claim6643

/-- The characteristic-zero polynomial ABC bound in the three-factor form. -/
theorem masonStothersPolynomialAbc
    {k : Type*} [Field k] [CharZero k] [DecidableEq k]
    {a b c : k[X]} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : IsCoprime a b) (_hbc : IsCoprime b c) (_hca : IsCoprime c a)
    (hsum : a + b + c = 0)
    (hnotconst : ¬(a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0)) :
    a.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      b.natDegree + 1 ≤ (radical (a * b * c)).natDegree ∧
      c.natDegree + 1 ≤ (radical (a * b * c)).natDegree := by
  rcases Polynomial.abc ha hb hc hab hsum with hdeg | hder
  · exact hdeg
  · rcases hder with ⟨hda, hdb, hdc⟩
    exfalso
    apply hnotconst
    exact ⟨Polynomial.derivative_eq_zero.mp hda,
      Polynomial.derivative_eq_zero.mp hdb,
      Polynomial.derivative_eq_zero.mp hdc⟩

end MathlibPlus.NumberTheory.Claim6643
