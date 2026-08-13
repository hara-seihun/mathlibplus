import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory.Claim9149

open Polynomial

/-- Claim 9149: the initial values of the integer trace-Chebyshev sequence. -/
theorem traceChebyshev_initial_claim9149 :
    Polynomial.Chebyshev.C ℤ 0 = 2 ∧
      Polynomial.Chebyshev.C ℤ 1 = X := by
  simp

/-- Claim 9149: the displayed trace-Chebyshev recurrence. -/
theorem traceChebyshev_recurrence_claim9149 (m : ℕ) :
    Polynomial.Chebyshev.C ℤ (m + 2) =
      X * Polynomial.Chebyshev.C ℤ (m + 1) -
        Polynomial.Chebyshev.C ℤ m := by
  exact Polynomial.Chebyshev.C_add_two ℤ (m : ℤ)

end MathlibPlus.NumberTheory.Claim9149
