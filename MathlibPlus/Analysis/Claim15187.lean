import Mathlib

namespace MathlibPlus.Analysis.Claim15187

/-- Algebraic Uvarov norm update.  The packet's undefined `ĥ` is represented
by a local definition; the item-2 recurrence for `eta` and the nonzero
hypotheses needed for division are made explicit because no source carrier is
defined in the claim text. -/
theorem uvarovNormFormula_claim15187
    (h lambda eta : ℕ → ℝ) (alpha : ℝ)
    (hη : ∀ n, eta n ≠ 0)
    (hh : ∀ n, h n ≠ 0)
    (hrec : ∀ n, eta (n + 1) = eta n + alpha * lambda n ^ 2 / h n) :
    ∀ n, let hhat := h n + alpha * lambda n ^ 2 / eta n
      hhat = h n * eta (n + 1) / eta n := by
  intro n
  dsimp
  rw [hrec]
  field_simp [hη n, hh n]

end MathlibPlus.Analysis.Claim15187
