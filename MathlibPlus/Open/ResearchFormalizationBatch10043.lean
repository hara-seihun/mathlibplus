import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a000eb03937c429c8f533ab1b48622

namespace MathlibPlus.Open.ResearchFormalizationBatch01

noncomputable def cornerLogarithmicDerivative {d : ℕ}
    (p : Fin d → ℕ) (M : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  -deriv (cornerQuotient p M c) s / cornerQuotient p M c s

/-- The full-corner quotient has no nonzero imaginary period for its logarithmic derivative. -/
def claim10043 : Prop :=
  ∀ (d M : ℕ) (p : Fin d → ℕ) (c : ℝ),
    2 ≤ d →
    1 ≤ M →
    (∀ j, Nat.Prime (p j)) →
    Function.Injective p →
    ∀ T : ℝ,
      T ≠ 0 →
      ¬ (∀ s : ℂ,
        cornerLogarithmicDerivative p M c (s + (T : ℂ) * Complex.I) =
          cornerLogarithmicDerivative p M c s)

end MathlibPlus.Open.ResearchFormalizationBatch01
