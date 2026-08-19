import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.ZetaReflectionClaim3830

/-- The uncompleted Riemann zeta function does not satisfy reflection
invariance. -/
def uncompletedZetaNotReflectionInvariant_claim3830 : Prop :=
  ¬ ∀ s : ℂ, riemannZeta s = riemannZeta (1 - s)

end MathlibPlus.Open.ResearchFormalization.ZetaReflectionClaim3830
