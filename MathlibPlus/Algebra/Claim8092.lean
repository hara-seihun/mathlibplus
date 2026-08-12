import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BigOperators

namespace MathlibPlus.Algebra.Claim8092

/-- Pairwise strict cofactor dominance makes the finite alternating boundary sum
positive.  The source packet fixes `α = 1/4` in its displayed application; the
formal lemma keeps the stated pairwise hypothesis and therefore works for every
real `α`. -/
theorem pairwiseCofactorBoundary
    (α : ℝ) (r : ℕ) (Δ : ℕ → ℝ)
    (hΔ : ∀ m ≤ r, 0 < Δ m)
    (hpair : ∀ m < r, α * Δ (m + 1) < Δ m) :
    0 < ∑ m ∈ Finset.range (r + 1), (-α) ^ m * Δ m := by
  have factor : ∀ (c : ℝ) (s : ℕ) (f : ℕ → ℝ),
      (∑ m ∈ Finset.range s, c * f m) =
        c * (∑ m ∈ Finset.range s, f m) := by
    intro c s f
    induction s with
    | zero => simp
    | succ s ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  have aux : ∀ (s : ℕ) (d : ℕ → ℝ),
      (∀ m ≤ s, 0 < d m) →
      (∀ m < s, α * d (m + 1) < d m) →
      0 < ∑ m ∈ Finset.range (s + 1), (-α) ^ m * d m := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro d hd hp
        rcases s with _ | _ | s
        · simpa using hd 0 (by omega)
        · have hp0 : α * d 1 < d 0 := hp 0 (by omega)
          simpa [Finset.sum_range_succ] using (show 0 < d 0 - α * d 1 by linarith)
        · have hd_tail : ∀ m ≤ s, 0 < d (m + 2) := by
            intro m hm
            exact hd (m + 2) (by omega)
          have hp_tail : ∀ m < s,
              α * d (m + 2 + 1) < d (m + 2) := by
            intro m hm
            exact hp (m + 2) (by omega)
          have htail := ih s (by omega) (fun m => d (m + 2))
            hd_tail hp_tail
          have hpair01 : 0 < d 0 - α * d 1 := by
            linarith [hp 0 (by omega)]
          have htail_nonneg :
              0 ≤ α ^ 2 * (∑ m ∈ Finset.range (s + 1),
                (-α) ^ m * d (m + 2)) := by
            exact mul_nonneg (sq_nonneg α) (le_of_lt htail)
          have hfirst :
              (∑ m ∈ Finset.range 2, (-α) ^ m * d m) = d 0 - α * d 1 := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]
            norm_num
            ring
          have hfactor :
              (∑ m ∈ Finset.range (s + 1), (-α) ^ (2 + m) * d (2 + m)) =
                α ^ 2 * (∑ m ∈ Finset.range (s + 1),
                  (-α) ^ m * d (m + 2)) := by
            calc
              (∑ m ∈ Finset.range (s + 1), (-α) ^ (2 + m) * d (2 + m)) =
                  ∑ m ∈ Finset.range (s + 1),
                    α ^ 2 * ((-α) ^ m * d (m + 2)) := by
                apply Finset.sum_congr rfl
                intro m hm
                rw [pow_add]
                norm_num
                ring
              _ = α ^ 2 * (∑ m ∈ Finset.range (s + 1),
                    (-α) ^ m * d (m + 2)) :=
                factor (α ^ 2) (s + 1) (fun m => (-α) ^ m * d (m + 2))
          have hsplit :
              ∑ m ∈ Finset.range (s + 3), (-α) ^ m * d m =
                (d 0 - α * d 1) + α ^ 2 *
                  (∑ m ∈ Finset.range (s + 1),
                    (-α) ^ m * d (m + 2)) := by
            rw [show s + 3 = 2 + (s + 1) by omega, Finset.sum_range_add]
            rw [hfirst]
            convert congrArg (fun x => (d 0 - α * d 1) + x) hfactor using 1
          rw [hsplit]
          linarith
  exact aux r Δ hΔ hpair

end MathlibPlus.Algebra.Claim8092
