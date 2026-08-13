import Mathlib

/-!
# Classical zeta zero-free region

Statement-fidelity formalization of admitted claim 1761. The decimal denominator
is retained exactly as `4.824`; in Lean this is the rational `603 / 125`.
-/

namespace MathlibPlus.Open.AnalyticNumberTheory

/-- For every real `t ≥ 2`, the Riemann zeta function has no zero in the
half-plane `σ > 1 - 1 / (4.824 * log t)`. -/
def globalClassicalZetaZeroFreeRegion_claim1761 : Prop :=
  ∀ (t σ : ℝ),
    2 ≤ t →
      σ > 1 - 1 / ((4.824 : ℝ) * Real.log t) →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0

end MathlibPlus.Open.AnalyticNumberTheory
