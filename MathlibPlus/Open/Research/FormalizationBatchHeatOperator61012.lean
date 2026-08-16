import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch_01a00bf2_OrthogonalReflectionCompression

namespace MathlibPlus.Open.Research.FormalizationBatchHeatOperator61012

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch_01a00bf2

/-- The joint `(R_h,R_c)` eigenspace condition on the actual coefficient module. -/
def jointEigenspace (k : ℕ) (b : WeightBasis k) (ε η : ℂ) : Set (M k) :=
  {v |
    leftReversal k b v = ε • v ∧
      rightReversal k b v = η • v}

/-- The four joint projectors `E_(ε,η)`. -/
def jointProjector (k : ℕ) (b : WeightBasis k) (ε η : ℂ) : M k →ₗ[ℂ] M k :=
  ((4 : ℂ)⁻¹) •
    ((mixedIdentity k b + ε • leftReversal k b).comp
      (mixedIdentity k b + η • rightReversal k b))

/-- The finite heat operator on `M_k`. -/
def heatOperator (k : ℕ) (b : WeightBasis k) (lam : ℂ) : M k →ₗ[ℂ] M k :=
  ((4 : ℂ)⁻¹) •
    ((1 + lam) • (mixedIdentity k b + longestOperator k b) +
      (1 - lam) • (leftReversal k b + rightReversal k b))

/-- The four-sector multiplier list, written as a function of the two signs. -/
def heatMultiplier (lam ε η : ℂ) : ℂ :=
  if ε = 1 ∧ η = 1 then 1 else
    if ε = -1 ∧ η = -1 then lam else 0

/-- Two-sided inverse on the range of a projector. -/
def inverseOnRange {W : Type*} [AddCommGroup W] [Module ℂ W]
    (A B P : W →ₗ[ℂ] W) : Prop :=
  ∀ v : W, v ∈ LinearMap.range P →
    B (A v) = v ∧ A (B v) = v

/-- The exact corrected all-degree finite heat-operator statement. -/
def claim61012 : Prop :=
  (∀ (k : ℕ) (b : WeightBasis k),
    (leftReversal k b).comp (rightReversal k b) = longestOperator k b ∧
      (rightReversal k b).comp (leftReversal k b) = longestOperator k b ∧
        arthurProjector k b =
          jointProjector k b 1 1 + jointProjector k b (-1) (-1) ∧
    (∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      heatOperator k b (lam : ℂ) =
          jointProjector k b 1 1 +
            (lam : ℂ) • jointProjector k b (-1) (-1) ∧
        (∀ ε η : ℂ, (ε = 1 ∨ ε = -1) → (η = 1 ∨ η = -1) →
          ∀ v ∈ jointEigenspace k b ε η,
            heatOperator k b (lam : ℂ) v =
              heatMultiplier (lam : ℂ) ε η • v)) ∧
    (∀ lam μ : ℝ, 0 ≤ lam → lam ≤ 1 → 0 ≤ μ → μ ≤ 1 →
      (heatOperator k b (lam : ℂ)).comp (heatOperator k b (μ : ℂ)) =
        heatOperator k b ((lam * μ : ℝ) : ℂ)) ∧
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      LinearMap.range (heatOperator k b (lam : ℂ)) =
        LinearMap.range (arthurProjector k b) ∧
      inverseOnRange (W := M k)
        (heatOperator k b (lam : ℂ))
        (jointProjector k b 1 1 +
          (lam⁻¹ : ℂ) • jointProjector k b (-1) (-1))
        (arthurProjector k b)) ∧
    (0 < k →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
        ¬ Function.Bijective (heatOperator k b (lam : ℂ)))) ∧
  (∀ (b : WeightBasis 0) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    leftReversal 0 b = mixedIdentity 0 b ∧
      rightReversal 0 b = mixedIdentity 0 b ∧
        longestOperator 0 b = mixedIdentity 0 b ∧
          heatOperator 0 b (lam : ℂ) = mixedIdentity 0 b)

end

end MathlibPlus.Open.Research.FormalizationBatchHeatOperator61012
