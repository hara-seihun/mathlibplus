import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def projectiveRatio (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  -X z / D z

noncomputable def logarithmicDerivativeDifference
    (X D : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv X z / X z - deriv D z / D z

def projectiveDoubleZeroDiscriminant_15389 : Prop :=
  ∀ (X D : ℂ → ℂ) (z : ℂ),
    DifferentiableAt ℂ X z → DifferentiableAt ℂ D z →
    X z ≠ 0 → D z ≠ 0 →
      (X z + D z = 0 →
        deriv (fun w : ℂ => X w + D w) z =
          X z * logarithmicDerivativeDifference X D z) ∧
      ((X z + D z = 0 ∧
          deriv (fun w : ℂ => X w + D w) z = 0) ↔
        (projectiveRatio X D z = 1 ∧
          logarithmicDerivativeDifference X D z = 0))

end MathlibPlus.Open.ResearchFormalization
