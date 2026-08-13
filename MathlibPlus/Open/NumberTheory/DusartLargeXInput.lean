import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- The admitted claim 1063, with the real prime-counting function represented by
`Nat.primeCounting ⌊x⌋₊` and the terminating decimal `7.59` represented exactly
as `759 / 100`. -/
def dusartLargeXInput_claim1063 : Prop :=
  ∀ x : ℝ, 10 ^ (19 : ℕ) ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      (x / Real.log x) *
        (1 + 1 / Real.log x + 2 / (Real.log x) ^ 2 +
          (759 / 100 : ℝ) / (Real.log x) ^ 3)

end MathlibPlus.Open.NumberTheory
