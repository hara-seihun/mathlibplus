import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Logistic

noncomputable section


def compactlySupported (w : ℝ → ℝ) : Prop :=
  IsCompact (closure (Function.support w))

def claim_3397 (σ η : ℝ) (w q f : ℝ → ℝ) : Prop :=
  compactlySupported w ∧
    ∀ u : ℝ,
      q u =
          (1 - ((2 * σ - 1) / (2 * (8192 : ℝ))) +
              ((2 * σ - 1) / (2 * (8192 : ℝ))) * Real.exp (-(8192 : ℝ) * u)) /
            (1 + Real.exp (-(2 * σ - 1) * u)) ∧
      f u = η * w (η * u) * q u

end

end MathlibPlus.Open.ResearchFormalization.Logistic
