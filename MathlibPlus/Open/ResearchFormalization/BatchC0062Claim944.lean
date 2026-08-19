import Mathlib
import MathlibPlus.Open.Research.Batch_01a00468_NumberTheory

namespace MathlibPlus.Open.ResearchFormalization.BatchC0062

open scoped BigOperators
open MathlibPlus.Open.Research.Batch_01a00468_NumberTheory

noncomputable section

/-- The exact consecutive-prime pair carrier used by the checked finite range. -/
def consecutivePrimePair944 (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧
    ∀ n : ℕ, p < n → n < q → ¬ Nat.Prime n

/-- The order-four requirement attached to a consecutive prime pair. -/
def orderFourGapRequirement944 (p q : ℕ) : ℝ :=
  ((q : ℝ) - (p : ℝ)) / (p : ℝ) * (Real.log (p : ℝ)) ^ 4

/-- Claim 944: the active order-four consecutive-prime gap is `1327 < 1361`.
The finite comparison is the checked range below `17051708`, after which the
order-three-to-order-four bridge supplies the interval handoff. -/
def exactActiveOrderFourPrimeGap_claim944 : Prop :=
  let B₄ : ℝ := orderFourCoefficient
  let active := orderFourGapRequirement944 1327 1361
  let runnerUp := orderFourGapRequirement944 113 127
  consecutivePrimePair944 1327 1361 ∧
    active = B₄ ∧
    (∀ p q : ℕ, consecutivePrimePair944 p q → p < 17051708 →
      orderFourGapRequirement944 p q ≤ B₄ ∧
        (orderFourGapRequirement944 p q = B₄ ↔
          p = 1327 ∧ q = 1361)) ∧
    consecutivePrimePair944 113 127 ∧
    (∀ p q : ℕ, consecutivePrimePair944 p q → p < 17051708 →
      ¬ (p = 1327 ∧ q = 1361) →
      orderFourGapRequirement944 p q ≤ runnerUp ∧
        (orderFourGapRequirement944 p q = runnerUp ↔
          p = 113 ∧ q = 127)) ∧
    runnerUp < B₄ ∧ B₄ - runnerUp > (66216 : ℝ) / 10000

end

end MathlibPlus.Open.ResearchFormalization.BatchC0062
