import Mathlib.NumberTheory.Chebyshev

/-!
# FKS admissible envelope

Definitions corresponding to admitted claim 765.  The stated range and signed
error are explicit arguments to the admissibility predicate; no unmentioned
range is silently selected.
-/

namespace MathlibPlus.AnalyticNumberTheory.PrimeCounting

/-- The FKS envelope with amplitude `A` and the fixed source parameters. -/
noncomputable def fksEnvelope (A x : ℝ) : ℝ :=
  A * Real.rpow (Real.log x / (55666305 / 10000000 : ℝ)) (3 / 2 : ℝ) *
    Real.exp (-2 * Real.sqrt (Real.log x / (55666305 / 10000000 : ℝ)))

/-- A signed error is bounded by the FKS envelope on an explicit range. -/
def isAdmissibleSignedUpperBound
    (E : ℝ → ℝ) (A : ℝ) (range : Set ℝ) : Prop :=
  ∀ x : ℝ, x ∈ range → E x ≤ fksEnvelope A x

end MathlibPlus.AnalyticNumberTheory.PrimeCounting
