import Mathlib
import MathlibPlus.Open.Analysis.O0342PositivePowersLognormal

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.ResearchFormalizationO0342

noncomputable section

/-- Record 12's real Mellin transform, with the source exponent `z`. -/
noncomputable def lognormalMellin (σ z : ℝ) : ℝ :=
  MathlibPlus.Open.Analysis.O0342.lognormalConstant σ *
      Real.exp (σ ^ 2 * z ^ 2 / 2) *
    (Real.cos (2 * Real.pi * z) - 1)

/-- The atom of the completed carrier at the integer `n`.  The pushforward
identity uses the Mellin exponent `log n / log 2 - 1`. -/
noncomputable def completedPrimePowerAtom (σ : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * Real.log (n : ℝ) *
    lognormalMellin σ
      (Real.log (n : ℝ) / Real.log 2 - 1)

/-- The archimedean multiplier from the completed carrier. -/
noncomputable def completedKappa (t : ℝ) : ℝ :=
  t * ((Real.exp (2 * t) - 1)⁻¹ - Real.exp t)

/-- The continuum density obtained from Record 12 through the weighted
multiplicative pushforward. -/
noncomputable def completedContinuumDensity (σ t : ℝ) : ℝ :=
  completedKappa t *
    lognormalMellin σ (t / Real.log 2 - 1)

/-- Real numbers represented by integer exponents. -/
def isIntegerReal (z : ℝ) : Prop :=
  ∃ m : ℤ, z = (m : ℝ)

/-- Claim 15573: the explicit lognormal example has the full continuum sign
and dyadic zero tower, but its correctly shifted complete prime-power atom at
an odd prime power is strictly negative. -/
def lognormalOddPrimePowerFailure_claim15573 : Prop :=
  ∀ σ : ℝ,
    0 < σ →
      0 < MathlibPlus.Open.Analysis.O0342.lognormalConstant σ ∧
        (∀ z : ℝ,
          lognormalMellin σ z ≤ 0 ∧
            (lognormalMellin σ z = 0 ↔ isIntegerReal z)) ∧
        (∀ t : ℝ,
          Real.log 2 ≤ t →
            completedKappa t < 0 ∧
              0 ≤ completedContinuumDensity σ t) ∧
        (∀ k : ℕ,
          1 ≤ k →
            lognormalMellin σ ((k : ℝ) - 1) = 0 ∧
              completedPrimePowerAtom σ (2 ^ k) = 0 ∧
              completedPrimePowerAtom σ (2 ^ k) =
                (k : ℝ) * (Real.log 2) ^ 2 *
                  lognormalMellin σ ((k : ℝ) - 1)) ∧
        (∀ q k : ℕ,
          Nat.Prime q →
            q % 2 = 1 →
              1 ≤ k →
                let n : ℕ := q ^ k
                let z : ℝ := Real.log (n : ℝ) / Real.log 2
                ¬ isIntegerReal z ∧
                  lognormalMellin σ z < 0 ∧
                  lognormalMellin σ (z - 1) < 0 ∧
                  completedPrimePowerAtom σ n < 0) ∧
        ¬ (∀ n : ℕ, 2 ≤ n → 0 ≤ completedPrimePowerAtom σ n)

end
end MathlibPlus.Open.Analysis.ResearchFormalizationO0342
