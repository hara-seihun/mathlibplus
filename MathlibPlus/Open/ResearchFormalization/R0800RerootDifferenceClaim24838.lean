import MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibilityClaim24851

namespace MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility

/-- The reroot difference and its additive defect layers on the reviewed
finite labelled unrooted-tree carrier. -/
def rootedFactorRerootDifference_claim24838 : Prop :=
  ∀ (m : ℕ) (T : UnrootedTree m) (r s : Fin m),
    let Δ := rerootDifference T r s
    Δ = rootedForestPolynomial T r - rootedForestPolynomial T s ∧
      (∀ d : ℕ,
        defectLayer Δ d =
          defectLayer (rootedForestPolynomial T r) d -
            defectLayer (rootedForestPolynomial T s) d)

end MathlibPlus.Open.ResearchFormalization.R0800ContextualVisibility
