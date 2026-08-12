import Mathlib

namespace MathlibPlus.Algebra.Claim23994

/-- Closed forms for the order and side-valuation recurrences in claim 23994. -/
theorem crossed_iteration_closed_form_claim23994 (h d : ℕ → ℕ)
    (hh0 : h 0 = 11) (dd0 : d 0 = 1)
    (hrec : ∀ k, h (k + 1) = 6 * h k + 2)
    (drec : ∀ k, d (k + 1) = d k + 1) :
    ∀ k, h k = (57 * 6 ^ k - 2) / 5 ∧ d k = k + 1 := by
  have hmain : ∀ k, 5 * h k + 2 = 57 * 6 ^ k ∧
      h k = (57 * 6 ^ k - 2) / 5 ∧ d k = k + 1 := by
    intro k
    induction k with
    | zero =>
        simp [hh0, dd0]
    | succ k ih =>
        have hh := hrec k
        have hd := drec k
        rw [hh, hd, ih.2.2]
        constructor
        · rw [pow_succ]
          omega
        constructor
        · have hnum : 57 * 6 ^ k = 5 * h k + 2 := by omega
          have hnum' : 57 * (6 ^ k * 6) = (5 * h k + 2) * 6 := by
            calc
              57 * (6 ^ k * 6) = (57 * 6 ^ k) * 6 := by ring
              _ = (5 * h k + 2) * 6 := by rw [hnum]
          rw [pow_succ, hnum']
          omega
        · omega
  intro k
  exact ⟨(hmain k).2.1, (hmain k).2.2⟩

end MathlibPlus.Algebra.Claim23994
