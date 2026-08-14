import Mathlib

namespace MathlibPlus.Open.Research

/--
The exact integer feasibility elimination for the four neutral-support modes
at deficit seventeen.  The nonnegative variables `E`, `r`, and `W` are the
counts and trace mass from the admitted claim; `k` and `a` range over the
corresponding neutral-support counts.
-/
def neutralMultiplicityElimination26452 : Prop :=
  ∀ E r W : ℤ,
    0 ≤ E →
    0 ≤ r →
    0 ≤ W →
      ((2 * r ≥ E ∧ W ≤ E + 8) ↔
        ∃ k a : ℤ,
          k = 0 ∧
          a = 0 ∧
          2 * (a + r) ≥ k + E ∧
          2 * a + W ≤ k + E + 8) ∧
      (max 1 (W - E - 8) ≤ 2 * r - E ↔
        ∃ k a : ℤ,
          1 ≤ k ∧
          a = 0 ∧
          2 * (a + r) ≥ k + E ∧
          2 * a + W ≤ k + E + 8) ∧
      (max 1 (E - 2 * r) ≤ E + 8 - W ↔
        ∃ k a : ℤ,
          1 ≤ k ∧
          a = k ∧
          2 * (a + r) ≥ k + E ∧
          2 * a + W ≤ k + E + 8) ∧
      (W - E - 8 ≤ 2 * r - E ↔
        ∃ k a : ℤ,
          1 ≤ a ∧
          a < k ∧
          2 * (a + r) ≥ k + E ∧
          2 * a + W ≤ k + E + 8)

end MathlibPlus.Open.Research
