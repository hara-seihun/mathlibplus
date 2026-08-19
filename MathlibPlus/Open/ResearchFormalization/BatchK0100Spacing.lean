import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchK0100

/-- Claim 8524: the square relation between the original and lifted nodes
factors the corresponding consecutive spacing. -/
def claim8524_nodeSpacingTransfer : Prop :=
  ∀ (x y : ℕ → ℝ) (i : ℕ),
    x i = (y i) ^ 2 →
    x (i + 1) = (y (i + 1)) ^ 2 →
    x (i + 1) - x i =
      (y (i + 1) - y i) * (y (i + 1) + y i)

end MathlibPlus.Open.ResearchFormalization.BatchK0100
