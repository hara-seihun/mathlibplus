import MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibilityClaim24851

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility

noncomputable section
open Classical

/-- Claim 24849: a genuine rooted-forest context of weight `a` has the
canonical defect-zero component-size layer `x₁ᵃ`. -/
def defectZeroLayerOfGenuineContext_claim24849 : Prop :=
  ∀ (a : ℕ) (C : RootedForestContext),
    genuineContext a C →
      defectLayer (contextProduct C) 0 =
        Polynomial.C ((MvPolynomial.X 1) ^ a)

end

end MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility
