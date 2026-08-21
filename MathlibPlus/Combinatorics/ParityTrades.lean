-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics

/-- The two parity arrays from admitted claim 20796 have the same three
one-dimensional marginals.  The integer-valued `1 ± (-1)^...` form is retained
rather than replacing the arrays by an unlabelled multiset. -/
theorem parityTrades_marginals_claim20796 :
    let plus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
      fun p q r => 1 + (-1 : ℤ) ^ (p.val + q.val + r.val)
    let minus : Fin 2 → Fin 2 → Fin 2 → ℤ :=
      fun p q r => 1 - (-1 : ℤ) ^ (p.val + q.val + r.val)
    (∀ p : Fin 2,
        (∑ q : Fin 2, ∑ r : Fin 2, plus p q r) = 4 ∧
        (∑ q : Fin 2, ∑ r : Fin 2, minus p q r) = 4) ∧
      (∀ q : Fin 2,
        (∑ p : Fin 2, ∑ r : Fin 2, plus p q r) = 4 ∧
        (∑ p : Fin 2, ∑ r : Fin 2, minus p q r) = 4) ∧
      (∀ r : Fin 2,
        (∑ p : Fin 2, ∑ q : Fin 2, plus p q r) = 4 ∧
        (∑ p : Fin 2, ∑ q : Fin 2, minus p q r) = 4) := by
  native_decide

end MathlibPlus.Combinatorics
