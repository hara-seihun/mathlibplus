import Mathlib

namespace MathlibPlus.Open.Analysis.Claim1215Restatement

noncomputable section

private def denominator1215 (c x : ℝ) : ℝ :=
  Real.log x - 1 - c / Real.log x

private def ratio1215 (c x : ℝ) : ℝ :=
  x / denominator1215 c x

private def transferToRepairedCoefficient1215 : Prop :=
  ∀ {f : ℝ → ℝ} {X : ℝ},
    (∀ x : ℝ, X ≤ x → 1 < x) →
      (∀ x : ℝ, X ≤ x →
        0 < denominator1215 (1.149 : ℝ) x →
          f x < ratio1215 (1.149 : ℝ) x) →
        ∀ x : ℝ, X ≤ x →
          0 < denominator1215 (1.14900031 : ℝ) x →
            f x < ratio1215 (1.14900031 : ℝ) x

/-- Claim 1215: on the stated `x > 1` positive-denominator domain, the
coefficient direction is strict, and a bound at `1.149` transfers to the
repaired coefficient `1.14900031`. -/
def claim1215CoefficientMonotonicity : Prop :=
  (∀ (x c₁ c₂ : ℝ),
    1 < x →
      c₁ < c₂ →
        0 < denominator1215 c₁ x →
          0 < denominator1215 c₂ x →
            ratio1215 c₁ x < ratio1215 c₂ x) ∧
    transferToRepairedCoefficient1215

end

end MathlibPlus.Open.Analysis.Claim1215Restatement
