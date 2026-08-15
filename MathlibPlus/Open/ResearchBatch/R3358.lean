import Mathlib

noncomputable section
open MeasureTheory
open scoped BigOperators Interval

namespace MathlibPlus.Open.ResearchBatch.R3358

def divisorCount (n : ℕ) : ℕ := (Nat.divisors n).card
def offsetCondition (n j : ℕ) : Prop := divisorCount (n - j) ≤ j + 2
def sixOffsetConditions (n : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 6, offsetCondition n j

def sixOffsetReduction_claim48926 : Prop :=
  ∀ n : ℕ, n > 24 → sixOffsetConditions n →
    210 ∣ n ∧ Nat.Prime ((n - 6) / 6)

end MathlibPlus.Open.ResearchBatch.R3358
