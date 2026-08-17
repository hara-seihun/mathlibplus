import MathlibPlus.Open.FormalizationBatch.AdmittedClaims1158And1166

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

/-- The coefficient denominator used by the Table 8 fixed-half-line bound. -/
def predecessorPoleDenominator1177 (c x : ℝ) : ℝ :=
  Real.log x - c

/--
Claim 1177: the below-pole coefficient domain cannot be removed.  The
corrected coefficient-1.071 start supplies a concrete pole counterexample to
an unrestricted extension of the low-cell biconditional.
-/
def predecessorPoleRegime_claim1177 : Prop :=
  let n₁ : ℝ := 22078034
  let n₁Int : ℤ := 22078034
  let predecessor : ℝ := n₁ - 1
  let cPole : ℝ := Real.log predecessor
  (Nat.Prime 22078033) ∧
    MathlibPlus.Open.FormalizationBatch.table8PrimeCount predecessor =
      (1393895 : ℝ) ∧
    MathlibPlus.Open.FormalizationBatch.table8PrimeCount n₁ =
      (1393895 : ℝ) ∧
    predecessorPoleDenominator1177 cPole predecessor = 0 ∧
    (∀ c : ℝ,
      Real.log predecessor < c → c < Real.log n₁ →
        predecessorPoleDenominator1177 c predecessor < 0 ∧
        0 < predecessorPoleDenominator1177 c n₁) ∧
    ¬(
      MathlibPlus.Open.FormalizationBatch.table8LeastIntegerStart cPole n₁Int ↔
        (MathlibPlus.Open.FormalizationBatch.table8Alpha n₁ < cPole ∧
          cPole ≤
            MathlibPlus.Open.FormalizationBatch.table8PredecessorThreshold n₁))

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
