import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35784

open scoped BigOperators

private def binaryDigits {k : ℕ} (d : Fin k → ℕ) : Prop :=
  ∀ j, d j ≤ 1

private def prefixCarry (k : ℕ) (d : Fin k → ℕ) : ℤ :=
  14 * (2 : ℤ) ^ k -
    15 * ∑ j : Fin k,
      (j.val + 1 : ℤ) * (d j : ℤ) * (2 : ℤ) ^ (k - (j.val + 1))

private def centeredState (k : ℕ) (r : ℤ) : ℤ :=
  2 * r - 15 * ((k : ℤ) + 2)

private def record15Class (i : Fin 4) : ℤ :=
  match i.val with
  | 0 => -2
  | 1 => 11
  | 2 => -8
  | _ => -1

private def record15At (k : ℕ) : ℤ :=
  match k % 4 with
  | 0 => -2
  | 1 => 11
  | 2 => -8
  | _ => -1

/-- Claim 35784: a terminal boundary is excluded by the four-state
congruence invariant modulo `30`. -/
def terminalBoundaryExclusion_claim35784 : Prop :=
  ∀ (k : ℕ) (d : Fin k → ℕ),
    binaryDigits d →
      let s := centeredState k (prefixCarry k d)
      Int.ModEq 30 s (record15At k) ∧
        (∀ i : Fin 4, ¬ (15 : ℤ) ∣ record15Class i) ∧
        (|s| = (15 : ℤ) * ((k : ℤ) + 2) → (15 : ℤ) ∣ s) ∧
        |s| ≠ (15 : ℤ) * ((k : ℤ) + 2)

end MathlibPlus.Open.ResearchFormalization.R2777Claim35784
