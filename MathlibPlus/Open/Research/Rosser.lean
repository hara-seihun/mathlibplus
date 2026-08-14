import Mathlib

namespace MathlibPlus.Open.Research.Rosser

noncomputable section
open scoped BigOperators
local instance researchDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance researchDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Ordered prime products are represented by their descending prime sequence;
the squarefree condition is retained explicitly. -/
def descendingPrimeProduct (D z d : ℕ) : Prop :=
  d = 1 ∨
    ∃ k : ℕ, 1 ≤ k ∧ ∃ p : ℕ → ℕ,
      (∀ i, i < k → Nat.Prime (p i)) ∧
      (∀ i j, i < j → j < k → p j < p i) ∧
      (∀ i, i < k → p i < z) ∧
      d = ∏ i ∈ Finset.range k, p i ∧
      Squarefree d ∧
      (∀ j, 1 ≤ j → 2 * j ≤ k →
        (∏ i ∈ Finset.range (2 * j), p i) *
            (p (2 * j - 1)) ^ 2 < D)

def rosserLowerSupport (D z : ℕ) : Finset ℕ :=
  (Finset.range D).filter (descendingPrimeProduct D z)

def integerMobius (d : ℕ) : ℤ :=
  if Squarefree d then
    (-1 : ℤ) ^ (d.primeFactors.card)
  else 0

def rosserLowerWeight (D z d : ℕ) : ℤ :=
  if d ∈ rosserLowerSupport D z then integerMobius d else 0

def lowerRosserSupportClaim : Prop :=
  ∀ D z : ℕ, 64 ≤ D → 2 < z → z ≤ Nat.sqrt D →
    (1 ∈ rosserLowerSupport D z) ∧
    (∀ d ∈ rosserLowerSupport D z,
      d = 1 ∨
        ∃ k : ℕ, 1 ≤ k ∧ ∃ p : ℕ → ℕ,
          (∀ i, i < k → Nat.Prime (p i)) ∧
          (∀ i j, i < j → j < k → p j < p i) ∧
          (∀ i, i < k → p i < z) ∧
          d = ∏ i ∈ Finset.range k, p i ∧
          Squarefree d ∧
          (∀ j, 1 ≤ j → 2 * j ≤ k →
            (∏ i ∈ Finset.range (2 * j), p i) *
                (p (2 * j - 1)) ^ 2 < D)) ∧
    (∀ d, d ∈ rosserLowerSupport D z →
      rosserLowerWeight D z d = integerMobius d)

def toggleTwo (d : ℕ) : ℕ :=
  if 2 ∣ d then d / 2 else 2 * d

def toggleTwoRosserClaim : Prop :=
  ∀ D z : ℕ, 64 ≤ D → 2 < z → z ≤ Nat.sqrt D →
    (∀ d ∈ rosserLowerSupport D z, toggleTwo d ∈ rosserLowerSupport D z) ∧
    (∀ d ∈ rosserLowerSupport D z, toggleTwo (toggleTwo d) = d) ∧
    (∀ d ∈ rosserLowerSupport D z, toggleTwo d ≠ d) ∧
    (∀ d ∈ rosserLowerSupport D z,
      integerMobius (toggleTwo d) = -integerMobius d) ∧
    (∑ d ∈ rosserLowerSupport D z, rosserLowerWeight D z d) = 0

end
end MathlibPlus.Open.Research.Rosser
