import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35782

noncomputable section
open scoped BigOperators

private def binaryPrefix (d : ℕ → ℚ) : Prop :=
  ∀ j : ℕ, d j = 0 ∨ d j = 1

private def weightedPrefix (d : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1), (j : ℚ) * d j / (2 : ℚ) ^ j

private def prefixState (d : ℕ → ℚ) (N : ℕ) : ℚ :=
  (15 : ℚ) *
    (2 * ((2 : ℚ) ^ N * ((14 : ℚ) / 15 - weightedPrefix d N)) -
      (N + 2 : ℚ))

private def fourStateResidue (N : ℕ) : ℤ :=
  match N % 4 with
  | 0 => -2
  | 1 => 11
  | 2 => -8
  | _ => -1

/-- Claim 35782: every binary prefix in the exact `x=14/15` rational-state
carrier has the stated four-state congruence modulo `30`. -/
def claim_35782_fourStateCongruence : Prop :=
  ∀ d : ℕ → ℚ, binaryPrefix d →
    prefixState d 0 = -2 ∧
      ∀ N : ℕ, ∃ z : ℤ,
        prefixState d N = z ∧
          (30 : ℤ) ∣ z - fourStateResidue N

end

end MathlibPlus.Open.ResearchFormalization.R2777Claim35782
