import Mathlib

namespace MathlibPlus.Open.Combinatorics.Claim20756

open scoped BigOperators

/-- Claim 20756: the two parity arrays on the binary cube are distinct
nonnegative integer arrays with the same three one-dimensional marginals. -/
def claim20756 : Prop :=
  let tau : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => (-1 : ℤ) ^ (p.1 + q.1 + r.1)
  let tPlus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => 1 + tau p q r
  let tMinus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
    fun p q r => 1 - tau p q r
  (tPlus ≠ tMinus) ∧
    (∀ p q r, 0 ≤ tPlus p q r ∧
      (tPlus p q r = 0 ∨ tPlus p q r = 2)) ∧
    (∀ p q r, 0 ≤ tMinus p q r ∧
      (tMinus p q r = 0 ∨ tMinus p q r = 2)) ∧
    (∀ p : Fin 2,
      (∑ q : Fin 2, ∑ r : Fin 2, tPlus p q r) = 4 ∧
      (∑ q : Fin 2, ∑ r : Fin 2, tMinus p q r) = 4) ∧
    (∀ q : Fin 2,
      (∑ p : Fin 2, ∑ r : Fin 2, tPlus p q r) = 4 ∧
      (∑ p : Fin 2, ∑ r : Fin 2, tMinus p q r) = 4) ∧
    (∀ r : Fin 2,
      (∑ p : Fin 2, ∑ q : Fin 2, tPlus p q r) = 4 ∧
      (∑ p : Fin 2, ∑ q : Fin 2, tMinus p q r) = 4)

end MathlibPlus.Open.Combinatorics.Claim20756
