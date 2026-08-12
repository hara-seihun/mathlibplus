import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

namespace MathlibPlus.Algebra

/--
Claim 58522 (R-4734.5): the exact Frobenius second-difference exception in an
odd prime field.  The later congruence-class generalization in the source is
not silently identified with this first-layer statement.
-/
theorem claim58522_frobeniusSecondDifference
    (p : ℕ) [Fact p.Prime] (_hpodd : 2 < p) (s : ZMod p) :
    ((s + 2) ^ p - 2 * (s + 1) ^ p + s ^ p =
        (s + 2) - 2 * (s + 1) + s) ∧
      ((s + 2) - 2 * (s + 1) + s = 0) := by
  constructor
  · rw [add_pow_char s 2 p, add_pow_char s 1 p]
    simp [ZMod.pow_card]
  · ring

end MathlibPlus.Algebra
