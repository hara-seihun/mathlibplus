import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MathlibPlus.Open.NumberTheory.PrimeDigitSum

/-- Claim 1401: exact explicit decimal prime digit-sum surjectivity threshold. -/
noncomputable def decimalPrimeDigitSumSurjectivity : Prop :=
  ∀ m : ℕ,
    138033986655720044641496559943864 ≤ m →
    Nat.Coprime m 9 →
      ∃ p : ℕ,
        Nat.Prime p ∧
        (p : ℝ) ≤ (10 : ℝ) ^ ((2 : ℝ) * (m : ℝ) / 9) ∧
        (Nat.digits 10 p).sum = m

end MathlibPlus.Open.NumberTheory.PrimeDigitSum
