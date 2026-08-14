import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable def dualConstant_1559 : ℝ := 3 / 2 + Real.log 2

noncomputable def dualCertificate_1559 (u : ℝ) : ℝ :=
  1 + Real.log u - dualConstant_1559 * (u - 1)

def admissibleWeight_1559 (w : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) 2) ∧
    (∀ u ∈ Set.Icc (1 : ℝ) 2, 0 ≤ w u) ∧
    (∫ u in (1 : ℝ)..2, w u) = 1

noncomputable def fixedRangeNorm_1559 (w : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (w 2 / 2 + w 1 +
      (∫ u in (1 : ℝ)..2, w u / u) +
      (∫ u in (1 : ℝ)..2, |deriv w u| / u))

def dualIntegrationIdentityAndEqualityRigidity_1559 : Prop :=
  (∀ u ∈ Set.Ioo (1 : ℝ) 2,
      |dualCertificate_1559 u| < 1 / u) ∧
    ∀ w : ℝ → ℝ,
      admissibleWeight_1559 w →
        (w 1 + w 2 / 2 +
            (∫ u in (1 : ℝ)..2, w u / u) +
            (∫ u in (1 : ℝ)..2, dualCertificate_1559 u * deriv w u) =
          dualConstant_1559 * (∫ u in (1 : ℝ)..2, w u)) ∧
        (fixedRangeNorm_1559 w = dualConstant_1559 / (2 * Real.pi) →
          (∀ u ∈ Set.Ioo (1 : ℝ) 2, deriv w u = 0) ∧
          (∀ u ∈ Set.Icc (1 : ℝ) 2, w u = 1))

end MathlibPlus.Open.Analysis
