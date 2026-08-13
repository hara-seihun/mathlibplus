import Mathlib

namespace MathlibPlus.NumberTheory

/-- For a positive integer, the exponent data retained by an anonymized
factorization determines squarefreeness exactly. -/
theorem squarefree_iff_visible_exponents_claim9275 {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p : ℕ, n.factorization p ≤ 1 :=
  Nat.squarefree_iff_factorization_le_one hn

end MathlibPlus.NumberTheory
