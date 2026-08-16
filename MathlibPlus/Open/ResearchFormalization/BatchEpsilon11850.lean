import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchEpsilon11850

noncomputable section

open scoped BigOperators

/-- The positive-integer cutoff appearing in the Möbius--LCM sum. -/
def positiveCutoff (X : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊X⌋₊

/-- `S_ε(X) = ∑_{1≤d,e≤X} μ(d) μ(e) / [d,e]^(1+ε)`. -/
def S (ε X : ℝ) : ℝ :=
  ∑ d ∈ positiveCutoff X, ∑ e ∈ positiveCutoff X,
    (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) /
      Real.rpow (Nat.lcm d e : ℝ) (1 + ε)

/-- The global epsilon monotonicity assertion is false, with the exact
first-cutoff counterexample. -/
def globalEpsilonMonotonicityIsFalse : Prop :=
  (¬ (∀ X : ℝ, 0 < X → ∀ ε : ℝ, 0 ≤ ε → S ε X ≤ S 0 X)) ∧
  (∀ X ε : ℝ, 2 ≤ X → X < 3 → 0 < ε →
    S ε X - S 0 X = (1 - Real.rpow 2 (-ε)) / 2 ∧
    0 < S ε X - S 0 X)

end

end MathlibPlus.Open.ResearchFormalization.BatchEpsilon11850
