import Mathlib

namespace MathlibPlus.Open.Analysis

/--
Claim 11111: for a nonzero vector in a complex inner-product space, the
rank-one orthogonal projector and the source/complement coupling of a
self-adjoint operator are given by the displayed formulas.
-/
def claim11111_sourceLineProjectorAndResidual : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {v : E} (hv : v ≠ 0) (J : E →ₗ[ℂ] E),
    (∀ x y : E, inner ℂ (J x) y = inner ℂ x (J y)) →
      ∃ (P_v : E → E) (r : E),
        (∀ w : E,
          P_v w = (inner ℂ v w / inner ℂ v v) • v) ∧
        r = J v - P_v (J v)

end MathlibPlus.Open.Analysis
