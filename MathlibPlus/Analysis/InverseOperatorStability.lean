import Mathlib

namespace MathlibPlus.Analysis.InverseOperatorStability

/-- An invertible sampling operator controls coefficient size by the norm of its
inverse. The source's "generalized Vandermonde" operator is abstracted to an
arbitrary continuous linear equivalence because no construction of that operator
is included in the admitted claim. -/
theorem inverseOperatorStabilityCost
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (V : E ≃L[𝕜] F) (c : E) :
    ‖c‖ ≤ ‖V.symm.toContinuousLinearMap‖ * ‖V c‖ := by
  calc
    ‖c‖ = ‖V.symm (V c)‖ := by rw [V.symm_apply_apply]
    _ ≤ ‖V.symm.toContinuousLinearMap‖ * ‖V c‖ :=
      V.symm.toContinuousLinearMap.le_opNorm _

/-- The forward sampling error incurs the operator norm. -/
theorem forwardOperatorNormCost
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (V : E ≃L[𝕜] F) (c : E) :
    ‖V c‖ ≤ ‖V.toContinuousLinearMap‖ * ‖c‖ := by
  exact V.toContinuousLinearMap.le_opNorm c

/-- Combining the two estimates exposes the usual product of forward and
backward operator norms. -/
theorem forwardBackwardConditionCost
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (V : E ≃L[𝕜] F) (c : E) :
    ‖c‖ ≤
      (‖V.symm.toContinuousLinearMap‖ * ‖V.toContinuousLinearMap‖) * ‖c‖ := by
  calc
    ‖c‖ ≤ ‖V.symm.toContinuousLinearMap‖ * ‖V c‖ :=
      inverseOperatorStabilityCost V c
    _ ≤ ‖V.symm.toContinuousLinearMap‖ *
        (‖V.toContinuousLinearMap‖ * ‖c‖) :=
      mul_le_mul_of_nonneg_left (forwardOperatorNormCost V c) (norm_nonneg _)
    _ = (‖V.symm.toContinuousLinearMap‖ * ‖V.toContinuousLinearMap‖) * ‖c‖ := by
      ring

end MathlibPlus.Analysis.InverseOperatorStability
