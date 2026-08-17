import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3270

open scoped BigOperators

/-- The primorial appearing in the progression context. -/
def primeProduct (n : ℕ) : ℕ :=
  Finset.prod ((Finset.range (n + 1)).filter Nat.Prime) (fun p => p)

/-- The selected member `n₀ + i Q(y)` of the progression. -/
def progressionTerm (n₀ y i : ℕ) : ℕ :=
  n₀ + i * primeProduct y

/-- The complete interval and size context fixed for R-3270. -/
def progressionContext (x y k H n₀ : ℕ) : Prop :=
  x > y ∧
    y ≥ k ∧
    k ≥ 2 ∧
    H ≥ (k - 1) * primeProduct y + 1 ∧
    ∀ i : Fin k,
      1 ≤ progressionTerm n₀ y i.val ∧
        progressionTerm n₀ y i.val ≤ H

/-- Claim 46417: every prime at most `y` gives one residue to the selected
    progression. -/
def claim46417 : Prop :=
  ∀ (x y k H n₀ : ℕ),
    progressionContext x y k H n₀ →
      ∀ q : ℕ, Nat.Prime q → q ≤ y →
        ∀ i j : Fin k,
          progressionTerm n₀ y i.val % q =
            progressionTerm n₀ y j.val % q

/-- Claim 46420: for a prime strictly between `y` and `x`, the selected
    progression members have pairwise distinct residues. -/
def claim46420 : Prop :=
  ∀ (x y k H n₀ : ℕ),
    progressionContext x y k H n₀ →
      ∀ p : ℕ, Nat.Prime p → y < p → p ≤ x →
        ∀ i j : Fin k, i ≠ j →
          progressionTerm n₀ y i.val % p ≠
            progressionTerm n₀ y j.val % p

end MathlibPlus.Open.ResearchFormalization.R3270
