import MathlibPlus.Basic

namespace MathlibPlus.NumberTheory

/-!
Formalization of admitted claim 9160.  The endpoint `m ≥ 3` is retained
exactly; the conclusion is Euler's totient parity statement.
-/

/-- Euler's totient is even at every natural number at least three. -/
theorem totient_even_of_three_claim9160 (m : ℕ) (hm : 3 ≤ m) :
    Even (Nat.totient m) := by
  exact Nat.totient_even (by omega)

end MathlibPlus.NumberTheory
