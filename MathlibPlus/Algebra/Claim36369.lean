import Mathlib

namespace MathlibPlus.Algebra.Claim36369

open Polynomial

/-- The polynomial-domain cancellation core of claim 36369: two displayed
factor-count equations have the same nonzero right factor, so the powers of
an indeterminate agree and their exponents are equal. -/
theorem equalFactorCounts_claim36369
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (h : R[X]) (hh : h ≠ 0) (p q : ℕ)
    (hp : -(X : R[X]) ^ 2 = (X : R[X]) ^ q * h)
    (hq : -(X : R[X]) ^ 2 = (X : R[X]) ^ p * h) :
    p = q := by
  have hmul : (X : R[X]) ^ q * h = (X : R[X]) ^ p * h :=
    hp.symm.trans hq
  have hpow : (X : R[X]) ^ q = (X : R[X]) ^ p :=
    mul_right_cancel₀ hh hmul
  have hdegree := congrArg Polynomial.natDegree hpow
  simpa using hdegree.symm

end MathlibPlus.Algebra.Claim36369
