import Mathlib

namespace MathlibPlus.Open.Analysis.AgeFormalizationBatch

open scoped BigOperators

noncomputable section

/-- The finite set of positive integers m with m ≤ exp(v). -/
def ageIndexSet (v : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor (Real.exp v))

def reciprocalSquareRoot (m : ℕ) : ℝ :=
  (Real.sqrt (m : ℝ))⁻¹

/-- Claim 17455: the even age-jet definition. -/
def ageJet (n : ℕ) (v : ℝ) : ℝ :=
  2 * ∑ m ∈ ageIndexSet v,
    reciprocalSquareRoot m *
      (v - Real.log (m : ℝ)) ^ (2 * n) /
        (Nat.factorial (2 * n) : ℝ)

/-- Claim 17456: the odd age primitive, with denominator (2n)!. -/
def oddAgePrimitive (n : ℕ) (v : ℝ) : ℝ :=
  2 * ∑ m ∈ ageIndexSet v,
    reciprocalSquareRoot m *
      (v - Real.log (m : ℝ)) ^ (2 * n + 1) /
        (Nat.factorial (2 * n) : ℝ)

end
end MathlibPlus.Open.Analysis.AgeFormalizationBatch
