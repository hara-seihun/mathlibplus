import Mathlib
import MathlibPlus.Algebra.Claim8047_15332_8598_4985

namespace MathlibPlus.Open.ResearchFormalization.O0314

noncomputable section

open scoped BigOperators
open Set

/-- The common completion factor in the O-0314 pair. -/
noncomputable def standardCompletionFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) *
    (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The two exact even divisor factors in the centered coordinate. -/
noncomputable def lineQuartic (b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 + (b : ℂ) ^ 2) ^ 2

noncomputable def offQuartic (a b : ℝ) (z : ℂ) : ℂ :=
  (z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
    (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)

/-- The common `cosh` carrier and the two completed numerators. -/
noncomputable def coshCarrier (s : ℂ) : ℂ :=
  Complex.cosh (Real.pi * (s - 1 / 2))

noncomputable def completedLineNumerator (b : ℝ) (s : ℂ) : ℂ :=
  coshCarrier s * lineQuartic b (s - 1 / 2)

noncomputable def completedOffNumerator (a b : ℝ) (s : ℂ) : ℂ :=
  coshCarrier s * offQuartic a b (s - 1 / 2)

/-- The actual zeta-type pair, normalized by the displayed carrier `C(s)`. -/
noncomputable def completedLine (b : ℝ) (s : ℂ) : ℂ :=
  completedLineNumerator b s / standardCompletionFactor s

noncomputable def completedOff (a b : ℝ) (s : ℂ) : ℂ :=
  completedOffNumerator a b s / standardCompletionFactor s

/-- The order of a zero, retaining multiplicity through the first nonzero
iterated derivative. -/
noncomputable def zeroOrder (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  sInf {n : ℕ | iteratedDeriv n f s ≠ 0}

/-- Upper nontrivial zeros counted with their exact zero orders.  The explicit
completion factor is part of the carrier, and its nonzero condition prevents a
pole of the quotient from being counted as a zero. -/
noncomputable def upperZeroCount (f : ℂ → ℂ) (T : ℝ) : ℕ :=
  ∑' s : {s : ℂ // f s = 0 ∧
      0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧
      standardCompletionFactor s ≠ 0},
    zeroOrder f s.1

/-- The common carrier's upper zero count, without the completion denominator. -/
noncomputable def upperCoshCount (T : ℝ) : ℕ :=
  ∑' s : {s : ℂ // coshCarrier s = 0 ∧
      0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T},
    zeroOrder coshCarrier s.1

/-- The RH predicate for the nontrivial zeros of one explicit pair member. -/
def allNontrivialZerosOnLine (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → f s = 0 → s.re = 1 / 2

/-- `b` is generic for this pair when the common carrier and the displayed
quartic zeros are not cancelled by the common completion factor. -/
def genericHeight (a b : ℝ) : Prop :=
  coshCarrier ((1 / 2 + (b : ℂ) * Complex.I)) ≠ 0 ∧
    standardCompletionFactor ((1 / 2 + (b : ℂ) * Complex.I)) ≠ 0 ∧
    standardCompletionFactor ((1 / 2 + a : ℂ) + b * Complex.I) ≠ 0 ∧
    standardCompletionFactor ((1 / 2 - a : ℂ) + b * Complex.I) ≠ 0

/-- Claim 15339: the common cosh carrier and exact count do not determine the
critical-line location of the completed pair's divisors. -/
def claim15339 : Prop :=
  ∀ (a b : ℝ),
    0 < a → a < 1 / 2 → 0 < b → genericHeight a b →
      (∀ s : ℂ, coshCarrier s = 0 → s.re = 1 / 2) ∧
      (∀ T : ℝ, 0 ≤ T →
        upperZeroCount (completedLine b) T =
            upperCoshCount T + 2 * (if T ≥ b then 1 else 0) ∧
          upperZeroCount (completedOff a b) T =
            upperCoshCount T + 2 * (if T ≥ b then 1 else 0)) ∧
      allNontrivialZerosOnLine (completedLine b) ∧
      (¬ allNontrivialZerosOnLine (completedOff a b) ∧
        completedOff a b ((1 / 2 + a : ℂ) + b * Complex.I) = 0 ∧
        completedOff a b ((1 / 2 - a : ℂ) + b * Complex.I) = 0 ∧
        ((1 / 2 + a : ℂ) + b * Complex.I).re ≠ 1 / 2 ∧
        ((1 / 2 - a : ℂ) + b * Complex.I).re ≠ 1 / 2)

end

end MathlibPlus.Open.ResearchFormalization.O0314
