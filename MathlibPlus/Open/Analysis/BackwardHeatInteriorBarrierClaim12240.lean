import Mathlib

namespace MathlibPlus.Open

/-- The complete metric/interior certificate data described for Claim 12240. -/
def BackwardHeatInteriorCertificate_claim12240
    {Y : Type*} [MetricSpace Y]
    (D : ℝ → Y) (A : Set Y) (Good : ℝ → Prop) (η : ℝ) : Prop :=
  0 < η ∧
    (∀ τ : ℝ, -η < τ → τ ≤ 0 → D τ ∈ A → Good τ) ∧
    ContinuousWithinAt D (Set.Iic 0) 0 ∧
    D 0 ∈ interior A

/-- If Good fails at every negative time, no backward-heat interior certificate exists. -/
def metricInteriorBarrier_claim12240 : Prop :=
  ∀ {Y : Type*} [MetricSpace Y]
    (D : ℝ → Y) (A : Set Y) (Good : ℝ → Prop) (η : ℝ),
    (∀ τ : ℝ, τ < 0 → ¬ Good τ) →
      ¬ BackwardHeatInteriorCertificate_claim12240 D A Good η

end MathlibPlus.Open
