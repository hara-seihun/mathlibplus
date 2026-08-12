import Mathlib

namespace MathlibPlus.Algebra.MonicReciprocal

open Polynomial

/-- A monic polynomial of exact even natural degree whose polynomial reversal is
itself.  `Polynomial.reverse` is the coefficient-level formalization of
`X^(2*r) * f(X⁻¹)` in the source claim. -/
def IsMonicReciprocal {R : Type*} [Semiring R] (r : ℕ) (f : R[X]) : Prop :=
  f.Monic ∧ f.natDegree = 2 * r ∧ f.reverse = f

/-- The coefficients through degree `2*r` are palindromic. -/
def PalindromicCoefficients {R : Type*} [Semiring R] (r : ℕ) (f : R[X]) : Prop :=
  ∀ i ≤ 2 * r, f.coeff i = f.coeff (2 * r - i)

/-- The reversal definition is equivalent to the coefficient-palindrome
formulation, with the source's exact degree and monicity retained. -/
theorem isMonicReciprocal_iff_palindromic
    {R : Type*} [Semiring R] (r : ℕ) (f : R[X]) :
    IsMonicReciprocal r f ↔
      f.Monic ∧ f.natDegree = 2 * r ∧ PalindromicCoefficients r f := by
  constructor
  · rintro ⟨hmonic, hdeg, hrev⟩
    refine ⟨hmonic, hdeg, ?_⟩
    intro i hi
    have hcoeff := congrArg (fun p : R[X] => p.coeff i) hrev
    rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hi] at hcoeff
    exact hcoeff.symm
  · rintro ⟨hmonic, hdeg, hpal⟩
    refine ⟨hmonic, hdeg, ?_⟩
    ext i
    by_cases hi : i ≤ 2 * r
    · rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hi]
      exact (hpal i hi).symm
    · have hi' : f.natDegree < i := by
        rw [hdeg]
        exact Nat.lt_of_not_ge hi
      have hzero : f.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt hi'
      have hrevzero : f.reverse.coeff i = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt f.reverse_natDegree_le hi')
      exact hrevzero.trans hzero.symm

end MathlibPlus.Algebra.MonicReciprocal
