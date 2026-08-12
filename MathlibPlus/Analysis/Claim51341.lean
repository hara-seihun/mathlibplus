import Mathlib.Tactic

namespace MathlibPlus.Analysis

/-- The prefix-query reserve comparison from admitted claim 51341. -/
theorem prefixReserveLowerBound_claim51341 (Q : ℕ) (var : Fin Q → ℝ)
    (V R : ℝ) (hvar : ∀ s, var s ≤ V)
    (hR : (∑ s : Fin Q, (1 - var s)) ≤ R) :
    (∀ s, 1 - V ≤ 1 - var s) ∧ (Q : ℝ) * (1 - V) ≤ R := by
  constructor
  · intro s
    linarith [hvar s]
  · calc
      (Q : ℝ) * (1 - V) = ∑ _s : Fin Q, (1 - V) := by simp; ring
      _ ≤ ∑ s : Fin Q, (1 - var s) := by
        exact Finset.sum_le_sum (fun s _ => by linarith [hvar s])
      _ ≤ R := hR

end MathlibPlus.Analysis
