import Mathlib
import MathlibPlus.Combinatorics.BinaryCarry

namespace MathlibPlus.Open.ResearchFormalization.R2777Claim35785

open scoped BigOperators

private def binaryDigits {k : ℕ} (d : Fin k → ℕ) : Prop :=
  ∀ j, d j ≤ 1

private def prefixCarry (k : ℕ) (d : Fin k → ℕ) : ℤ :=
  14 * (2 : ℤ) ^ k -
    15 * ∑ j : Fin k,
      (j.val + 1 : ℤ) * (d j : ℤ) * (2 : ℤ) ^ (k - (j.val + 1))

private def centeredState (k : ℕ) (r : ℤ) : ℤ :=
  2 * r - 15 * ((k : ℤ) + 2)

/-- Claim 35785: while the current carry is feasible and the centered state
has magnitude above `15`, exactly one next bit is feasible and the magnitude
has the displayed update. -/
def forcedDigitAndMagnitude_claim35785 : Prop :=
  ∀ (k : ℕ) (d : Fin k → ℕ),
    binaryDigits d →
      let r := prefixCarry k d
      let s := centeredState k r
      0 ≤ r ∧ r ≤ (15 : ℤ) * ((k : ℤ) + 2) ∧ |s| > 15 →
        ∃ bit : Bool,
          MathlibPlus.Combinatorics.BinaryCarry.childFeasible k r bit ∧
            (∀ other : Bool,
              MathlibPlus.Combinatorics.BinaryCarry.childFeasible k r other ↔
                other = bit) ∧
            |centeredState (k + 1)
                (MathlibPlus.Combinatorics.BinaryCarry.nextCarry k r bit)| =
              |2 * |s| - (15 : ℤ) * ((k : ℤ) + 1)|

end MathlibPlus.Open.ResearchFormalization.R2777Claim35785
