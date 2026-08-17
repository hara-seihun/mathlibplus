import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2294

noncomputable section

open scoped BigOperators

/-- The Erdős-261 weight `w_j=j/2^j`. -/
def erdosWeight (j : ℕ) : ℚ :=
  (j : ℚ) / (2 : ℚ) ^ j

def firstSwapSupport (s : ℕ) : Finset ℕ :=
  {2 ^ (2 ^ s - 1) - (2 ^ s - 1)} ∪
    Finset.Icc
      (2 ^ (2 ^ s - 1) + (2 ^ s - 1) - s + 1)
      (2 ^ (2 ^ s - 1) + (2 ^ s - 1) - 1)

def secondSwapSupport (s : ℕ) : Finset ℕ :=
  Finset.Icc
      (2 ^ (2 ^ s - 1) - (2 ^ s - 1) + 1)
      (2 ^ (2 ^ s - 1) - 1) ∪
    {2 ^ (2 ^ s - 1) + (2 ^ s - 1) - s}

def swapSupport (s : ℕ) : Finset ℕ :=
  firstSwapSupport s ∪ secondSwapSupport s

def supportWeightSum (D : Finset ℕ) : ℚ :=
  D.sum erdosWeight

/-- Claim 44259: the displayed finite swaps have equal weight and their
supports are disjoint for distinct parameters, including the small identity. -/
def claim44259 : Prop :=
  (∀ s : ℕ, 2 ≤ s →
    supportWeightSum (firstSwapSupport s) =
        supportWeightSum (secondSwapSupport s) ∧
      ∀ t : ℕ, 2 ≤ t → t ≠ s →
        Disjoint (swapSupport s) (swapSupport t)) ∧
    erdosWeight 5 + erdosWeight 10 =
      erdosWeight 6 + erdosWeight 7 + erdosWeight 9

def signedFiniteSupport (D : Finset ℤ) (c : ℤ → ℤ) : Prop :=
  (∀ d : ℤ, c d = 0 ↔ d ∉ D) ∧
    ∀ d : ℤ, c d = -1 ∨ c d = 0 ∨ c d = 1

def translatedWeight (t : ℕ) (d : ℤ) : ℚ :=
  erdosWeight (Int.toNat ((t : ℤ) + d))

/-- Claim 44260: no nonzero finitely supported signed coefficient pattern
can give an identity for every sufficiently large translation. -/
def claim44260 : Prop :=
  ∀ (D : Finset ℤ) (c : ℤ → ℤ),
    signedFiniteSupport D c →
    (∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      (∀ d ∈ D, 0 < (t : ℤ) + d) ∧
        D.sum (fun d => (c d : ℚ) * translatedWeight t d) = 0) →
    ∀ d : ℤ, c d = 0

end

end MathlibPlus.Open.ResearchFormalization.R2294
