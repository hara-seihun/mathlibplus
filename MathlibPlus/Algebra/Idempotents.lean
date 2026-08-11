import MathlibPlus.Basic

/-!
# Idempotents in integral domains

Claim 26267 is formalized here at the level of the stated consequence: an
idempotent in the unspecified integral domain `A_F ⊗ A_F` is trivial.
The claim does not specify the construction of `A_F` or the field `F`, so the
ambient ring is represented by an arbitrary commutative ring without zero
divisors.
-/

namespace MathlibPlus.Algebra

/-- Every idempotent of a commutative ring without zero divisors is `0` or `1`. -/
theorem idempotent_eq_zero_or_one_of_noZeroDivisors
    {R : Type*} [CommRing R] [NoZeroDivisors R] (e : R) (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by
    calc
      e * (e - 1) = e * e - e := by ring
      _ = 0 := sub_eq_zero.mpr he
  rcases mul_eq_zero.mp h with he0 | he1
  · exact Or.inl he0
  · exact Or.inr (sub_eq_zero.mp he1)

end MathlibPlus.Algebra
