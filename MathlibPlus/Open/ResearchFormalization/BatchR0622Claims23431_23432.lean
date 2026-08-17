import Mathlib
import MathlibPlus.Algebra.Claim23430

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.BatchR0622Claims23431_23432

private def sampleVector (t : Fin 5) : Fin 3 → ℕ :=
  ![5 + t.1, 5 - t.1, 5]

private def falling (n k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, ((n - j : ℕ) : ℤ)

private def fallingMoment (a b c : ℕ) (t : Fin 5) : ℤ :=
  falling (sampleVector t 0) a *
    falling (sampleVector t 1) b *
      falling (sampleVector t 2) c

private def finiteDifferenceWeights : Fin 5 → ℤ :=
  fun t => (-1 : ℤ) ^ t.1 * (Nat.choose 4 t.1 : ℤ)

private def cubicRow (a b c : ℕ) : Fin 3 → ℕ := ![a, b, c]

/-- Claim 23431: the exact fourth finite-difference relation annihilates
all falling moments of total degree at most three on the five displayed
vectors, and its coefficient vector is the stated nonzero row. -/
def claim23431_fourthDifferenceCubicFallingMoments : Prop :=
  (∀ (a b c : ℕ), a + b + c ≤ 3 →
    (∑ t : Fin 5,
      finiteDifferenceWeights t * fallingMoment a b c t) = 0) ∧
    (∀ t : Fin 5,
      finiteDifferenceWeights t =
        (![1, -4, 6, -4, 1] : Fin 5 → ℤ) t) ∧
    ( (![1, -4, 6, -4, 1] : Fin 5 → ℤ) ≠ 0)

/-- Claim 23432: the four exact-total-degree-three rows with second exponent
zero and the three with second exponent one are strictly positive at every
one of the five displayed vectors. -/
def claim23432_sevenPositiveCubicRows : Prop :=
  (Set.ncard
      {α : Fin 3 → ℕ |
        (∑ i : Fin 3, α i) = 3 ∧ (α 1 = 0 ∨ α 1 = 1)} = 7) ∧
  (∀ (a c : ℕ), a + c = 3 →
    ∀ t : Fin 5, 0 < fallingMoment a 0 c t) ∧
  (∀ (a c : ℕ), a + c = 2 →
    ∀ t : Fin 5, 0 < fallingMoment a 1 c t)

end MathlibPlus.Open.ResearchFormalization.BatchR0622Claims23431_23432
