import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Q0132Claim16821

noncomputable section

/-- The number of positive divisors used by the record problem. -/
def tau (m : ℕ) : ℕ :=
  (Nat.divisors m).card

/-- The shifted divisor value `b(m) = m + τ(m)`. -/
def shiftedDivisorValue (m : ℕ) : ℕ :=
  m + tau m

/-- The current prefix record `R(x) = max_{1 ≤ m ≤ x} b(m)`. -/
def R (x : ℕ) : ℕ :=
  (Finset.Icc 1 x).sup shiftedDivisorValue

/-- The same record written in the strict-prefix normalization. -/
def M (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n - 1)).sup shiftedDivisorValue

/-- A width-two witness is exactly the record inequality at `n`. -/
def widthTwoWitness (n : ℕ) : Prop :=
  M n ≤ n + 2

/-- The diagonal `n + 2` has caught the current record before the next index
enters the prefix. -/
def diagonalCatchesPrefixRecord (n : ℕ) : Prop :=
  R (n - 1) ≤ n + 2

/-- The witness condition is exactly the prefix-record catch-up condition. -/
def recordCatchupFormulation_claim16821 : Prop :=
  ∀ n : ℕ, widthTwoWitness n ↔ diagonalCatchesPrefixRecord n

end
end MathlibPlus.Open.ResearchFormalization.Q0132Claim16821
