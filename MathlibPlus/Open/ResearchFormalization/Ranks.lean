import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The explicit sufficient Taylor-rank inequality from the Rouché margin. -/
def claim17445 : Prop :=
  ∀ (A τ R m_R : ℝ) (N : ℕ),
    0 < A →
    0 < τ →
    0 < R →
    0 < m_R →
    (N : ℝ) >
        (2 * τ * R + Real.log (2 * A / m_R)) / Real.log 2 - 1 →
      2 * A * Real.exp (2 * τ * R) *
          Real.rpow 2 (-((N : ℝ) + 1)) < m_R

end MathlibPlus.Open.ResearchFormalization
