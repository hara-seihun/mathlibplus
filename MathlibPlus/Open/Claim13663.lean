import MathlibPlus.Open.ResearchFormalizationBatch_01a00b32_2d33_75c6_950c_2bbedfebec9e

namespace MathlibPlus.Open

/-- Claim 13663: the four exact Segre-ray expectations of the Klein
operators. -/
def claim13663 : Prop :=
  ∀ (θ U Φ : ℝ),
    hermitianInner (zTheta θ U Φ)
        (tensorMatVec (1 : TensorMatrix) (zTheta θ U Φ)) =
      ((4 * Real.cosh U : ℝ) : ℂ) ∧
    hermitianInner (zTheta θ U Φ)
        (tensorMatVec (dOp θ) (zTheta θ U Φ)) =
      ((4 * Real.cos Φ : ℝ) : ℂ) ∧
    hermitianInner (zTheta θ U Φ)
        (tensorMatVec jOp (zTheta θ U Φ)) =
      ((-4 * Real.sinh U * Real.sin Φ : ℝ) : ℂ) ∧
    hermitianInner (zTheta θ U Φ)
        (tensorMatVec (nOp θ) (zTheta θ U Φ)) = 0

end MathlibPlus.Open
