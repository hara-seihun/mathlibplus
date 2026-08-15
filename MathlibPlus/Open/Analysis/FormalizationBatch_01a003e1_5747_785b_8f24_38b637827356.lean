import Mathlib

namespace MathlibPlus.Open.AxlerTail

noncomputable section

/-- The real start point used for the tail estimate. -/
def tailStart : ℝ := 45399074

/-- The number of prime natural numbers at most a real argument. -/
def primeCounting (x : ℝ) : ℝ :=
  (((Finset.range (Int.toNat (Int.floor x) + 1)).filter Nat.Prime).card : ℝ)

/-- Axler's audit function. -/
def audit (x : ℝ) : ℝ := Real.log x - x / primeCounting x

/-- The comparison polynomial from the explicit prime-counting bound. -/
def comparisonPolynomial (L : ℝ) : ℝ :=
  (7 / 100 : ℝ) * L ^ 3 - (93 / 100 : ℝ) * L ^ 2 - (545 / 100 : ℝ) * L + (81213 / 10000 : ℝ)

/-- The first derivative of the comparison polynomial. -/
def comparisonPolynomialFirstDerivative (L : ℝ) : ℝ :=
  (21 / 100 : ℝ) * L ^ 2 - (186 / 100 : ℝ) * L - (545 / 100 : ℝ)

/-- The second derivative of the comparison polynomial. -/
def comparisonPolynomialSecondDerivative (L : ℝ) : ℝ :=
  (42 / 100 : ℝ) * L - (186 / 100 : ℝ)

/--
The tail-cubic positivity calculation at `H = 45,399,074`, its propagation to
all larger logarithms, and the resulting uniform audit-function bound.
The displayed decimal values are retained as their stated decimal-prefix
intervals, while positivity and the tail conclusion are stated separately.
-/
def positivityOfTailCubicAndUniformTailBound : Prop :=
  let H : ℝ := tailStart
  let Hlog : ℝ := Real.log H
  let Q := comparisonPolynomial
  let Q' := comparisonPolynomialFirstDerivative
  let Q'' := comparisonPolynomialSecondDerivative
  (Q Hlog ≥ (65843130822220354136 : ℝ) / 10000000000000000000 ∧
      Q Hlog < (65843130822220354137 : ℝ) / 10000000000000000000 ∧
      0 < Q Hlog) ∧
    (Q' Hlog ≥ (270353063768340 : ℝ) / 10000000000000 ∧
      Q' Hlog < (270353063768341 : ℝ) / 10000000000000 ∧
      0 < Q' Hlog) ∧
    (Q'' Hlog ≥ (554502095185767 : ℝ) / 100000000000000 ∧
      Q'' Hlog < (554502095185768 : ℝ) / 100000000000000 ∧
      0 < Q'' Hlog) ∧
    StrictMono Q'' ∧
    (∀ L : ℝ, Hlog ≤ L →
      0 < Q L ∧ 0 < Q' L ∧ 0 < Q'' L) ∧
    (∀ x : ℝ, H ≤ x → audit x < (1070 : ℝ) / 1000)

end

end MathlibPlus.Open.AxlerTail
