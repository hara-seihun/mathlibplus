import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0132Claim16817

noncomputable section

/-- The number of positive divisors used by the record problem. -/
def tau (m : ℕ) : ℕ :=
  (Nat.divisors m).card

/-- The shifted divisor value `b(m) = m + τ(m)`. -/
def shiftedDivisorValue (m : ℕ) : ℕ :=
  m + tau m

/-- The prefix record over positive indices at most `x`. -/
def prefixRecord (x : ℕ) : ℕ :=
  (Finset.Icc 1 x).sup shiftedDivisorValue

/-- `M(n) = max_{1 ≤ m < n} (m + τ(m))`. -/
def M (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sup shiftedDivisorValue

/-- The witness predicate used by the divisor-record question. -/
def widthTwoWitness (n : ℕ) : Prop :=
  M n ≤ n + 2

/-- The unresolved question about a witness strictly larger than `24`, recorded
as a predicate rather than asserted as either an existence or a nonexistence. -/
def strictlyLargerWitnessQuestion : Prop :=
  ∃ n : ℕ, 24 < n ∧ widthTwoWitness n

/-- The boundary witness `n = 24` satisfies `M(24) ≤ 26`. -/
def boundaryWitness_claim16817 : Prop :=
  widthTwoWitness 24

end
end MathlibPlus.Open.ResearchFormalization.Q0132Claim16817
