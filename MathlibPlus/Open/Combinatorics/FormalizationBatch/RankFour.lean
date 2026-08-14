import Mathlib

namespace MathlibPlus.Open.Combinatorics.FormalizationBatch

/-- The polynomial P displayed in claims 12543--12548. -/
def rankFourPolynomial (ε : ℝ) : ℝ :=
  2097152 * ε ^ 7 +
    55500425216 * ε ^ 6 -
    17984666444304 * ε ^ 5 +
    54202816766341 * ε ^ 4 -
    1270038175574324 * ε ^ 3 +
    1555972249399296 * ε ^ 2 -
    9009293588168704 * ε +
    9007199254740992

/-- Claim 12544: P has precisely one positive root in each displayed interval
and no other positive root. -/
def rankFourPositiveRootCount : Prop :=
  (∃! r : ℝ,
    (33 : ℝ) / 32 < r ∧ r < (17 : ℝ) / 16 ∧ rankFourPolynomial r = 0) ∧
  (∃! r : ℝ,
    (317 : ℝ) < r ∧ r < (318 : ℝ) ∧ rankFourPolynomial r = 0) ∧
  ∀ r : ℝ, 0 < r → rankFourPolynomial r = 0 →
    ((33 : ℝ) / 32 < r ∧ r < (17 : ℝ) / 16) ∨
      ((317 : ℝ) < r ∧ r < (318 : ℝ))

/-- Claim 12548: the polynomial is positive at the canonical shell-two
amplitude, with the exact radical value stated in the packet. -/
def rankFourCanonicalAmplitudePositive : Prop :=
  rankFourPolynomial (1 / Real.sqrt 2) =
      (39194972084741509 : ℝ) / 4 - 4824404421152399 * Real.sqrt 2 ∧
    (39194972084741509 : ℝ) / 4 - 4824404421152399 * Real.sqrt 2 > 0

end MathlibPlus.Open.Combinatorics.FormalizationBatch
