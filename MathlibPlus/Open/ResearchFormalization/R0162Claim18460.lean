import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0162Claim18460

/-- The absolute function in the relative quotient construction. -/
noncomputable def relativeA (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * H (t ^ 2)

/-- The companion function in the relative quotient construction. -/
noncomputable def relativeC (E : ℝ → ℝ) (t : ℝ) : ℝ :=
  t * E (t ^ 2)

/-- The relative quotient `J(t)=E(t²)/H(t²)`. -/
noncomputable def relativeQuotient (H E : ℝ → ℝ) (t : ℝ) : ℝ :=
  E (t ^ 2) / H (t ^ 2)

/-- The Wronskian convention `W[A,C]=AC'-A'C`. -/
noncomputable def relativeWronskian (A C : ℝ → ℝ) (t : ℝ) : ℝ :=
  A t * deriv C t - deriv A t * C t

/-- Claim 18460: the quotient identity and strict negative relative derivative
imply the asserted negative Wronskian orientation wherever `A` is nonzero. -/
def negativeRelativeWronskianOrientation18460 : Prop :=
  ∀ (H E : ℝ → ℝ),
    (∀ t : ℝ, 0 < t →
      DifferentiableAt ℝ (relativeQuotient H E) t ∧
        deriv (relativeQuotient H E) t < 0) →
    (∀ t : ℝ, 0 < t → relativeA H t ≠ 0 →
      relativeWronskian (relativeA H) (relativeC E) t =
        relativeA H t ^ 2 * deriv (relativeQuotient H E) t) →
    ∀ t : ℝ, 0 < t → relativeA H t ≠ 0 →
      relativeWronskian (relativeA H) (relativeC E) t < 0

end MathlibPlus.Open.ResearchFormalization.R0162Claim18460
