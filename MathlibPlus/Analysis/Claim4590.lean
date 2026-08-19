import Mathlib

namespace MathlibPlus.Analysis

noncomputable section

/-- Claim 4590: at every fixed positive finite Pólya-frequency order, the
Schoenberg sector angle has no positive degree-uniform lower bound. -/
def claim4590_fixedPositivePFOrderSectorLimit : Prop :=
  ∀ r : ℕ, 0 < r →
    Filter.Tendsto
        (fun d : ℕ =>
          (Real.pi * (r : ℝ)) /
            ((d : ℝ) + (r : ℝ) - 1))
        Filter.atTop (nhds (0 : ℝ)) ∧
      ¬ ∃ δ : ℝ,
        0 < δ ∧
          ∀ d : ℕ,
            δ ≤
              (Real.pi * (r : ℝ)) /
                ((d : ℝ) + (r : ℝ) - 1)

end

end MathlibPlus.Analysis
