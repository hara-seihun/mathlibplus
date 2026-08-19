import MathlibPlus.Open.Basic

namespace MathlibPlus.Open.Analysis

/-- Claim 2485: elimination of the scale at a real double-zero wall. -/
def realDoubleZeroDiscriminant_claim2485 : Prop :=
  ∀ (F₀ C : ℝ → ℝ) (x s F₀' C' : ℝ),
    HasDerivAt F₀ F₀' x →
    HasDerivAt C C' x →
    C x ≠ 0 →
      ((F₀ x + s * C x = 0 ∧ F₀' + s * C' = 0) ↔
        (F₀' * C x - F₀ x * C' = 0 ∧ s = -F₀ x / C x))

/-- Claim 2488: positive real scales on a horizontal complex edge are
characterized by collinearity and the sign of the real quotient. -/
def positiveScaleHorizontalEdge_claim2488 : Prop :=
  ∀ (Y x : ℝ) (F₀ C : ℂ → ℂ) (z : ℂ),
    z = (x : ℂ) + Complex.I * (Y : ℂ) →
    C z ≠ 0 →
      ((∃ s : ℝ, 0 < s ∧ F₀ z + (s : ℂ) * C z = 0) ↔
        (Complex.im (F₀ z * starRingEnd ℂ (C z)) = 0 ∧
          0 < -(F₀ z / C z).re)) ∧
      (∀ s : ℝ, 0 < s →
        F₀ z + (s : ℂ) * C z = 0 →
        s = -(F₀ z / C z).re)

end MathlibPlus.Open.Analysis
