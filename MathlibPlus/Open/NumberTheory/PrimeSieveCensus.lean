import Mathlib

namespace MathlibPlus.Open.NumberTheory.PrimeSieveCensus

/-- The finite prime sieve count and the resulting low-range order-four
interval, with the exact coefficient from the admitted interval theorem. -/
def finiteSieveCover_claim946 : Prop :=
  let B₄ : ℝ := (34 / 1327 : ℝ) * (Real.log 1327) ^ 4
  (Finset.filter Nat.Prime (Finset.Icc 2 17051887)).card = 1094422 ∧
    ∀ x : ℝ, 2 ≤ x → x ≤ 17051708 →
      ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x * (1 + B₄ / (Real.log x) ^ 4)

end MathlibPlus.Open.NumberTheory.PrimeSieveCensus
