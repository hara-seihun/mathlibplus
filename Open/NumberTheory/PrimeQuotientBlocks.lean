import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NumberTheory.PrimeQuotientBlocks

/--
Claim 13374.  The quotient block is restricted to positive `r`, which is the
standard domain for `N / r` blocks carrying the `φ(r) / r` and remainder
weights.  The source's `q ≤ √N / 4` is represented over `ℝ`; the asserted
singleton reduction and both weight identities remain one registry node.
-/
noncomputable def primeQuotientBlockSingleton_claim13374 : Prop :=
  ∀ (N q : ℕ), Nat.Prime q →
    (q : ℝ) ≤ Real.sqrt (N : ℝ) / 4 →
      let quotientBlock : ℕ → ℕ → Finset ℕ := fun N d =>
        (Finset.Icc 1 N).filter (fun r => N / r = d)
      let totientWeight : ℕ → ℕ → ℝ := fun N d =>
        ∑ r ∈ quotientBlock N d,
          (Nat.totient r : ℝ) / (r : ℝ)
      let remainderWeight : ℕ → ℝ := fun r =>
        1 - 1 / (r : ℝ) ^ 2
      let reciprocalSquareWeight : ℕ → ℕ → ℝ := fun N d =>
        ∑ r ∈ quotientBlock N d, remainderWeight r
      quotientBlock N (N / q) = {q} ∧
        totientWeight N (N / q) =
          (Nat.totient q : ℝ) / (q : ℝ) ∧
        (Nat.totient q : ℝ) / (q : ℝ) = 1 - 1 / (q : ℝ) ∧
        reciprocalSquareWeight N (N / q) = remainderWeight q ∧
        remainderWeight q = 1 - 1 / (q : ℝ) ^ 2

end MathlibPlus.Open.NumberTheory.PrimeQuotientBlocks
