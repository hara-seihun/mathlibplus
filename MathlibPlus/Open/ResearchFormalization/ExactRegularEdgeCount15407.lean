import Mathlib
import MathlibPlus.Open.ResearchFormalization.GlobalProjectiveStokesGraphInequality15408

open scoped BigOperators ComplexConjugate Topology

namespace MathlibPlus.Open.ResearchFormalization.ExactRegularEdgeCount15407

open MathlibPlus.Open.ResearchFormalization.GlobalProjectiveStokesGraphInequality15408

/-- Claim 15407: after the finitely many closed regular components are
removed from the concrete Record 10 crossing graph, the remaining regular
edge count is the boundary half-edge contribution plus the critical loads. -/
def exactRegularEdgeCount_claim15407 : Prop :=
  ∀ (D : Set ℂ) (S B : ℂ → ℂ) (boundary : ℝ → ℂ)
    (edgeCount loopCount : ℕ)
    (edges : Fin edgeCount → ℝ → ℂ)
    (loops : Fin loopCount → ℝ → ℂ)
    (V : Finset ℂ),
    projectiveStokesRecord10
      D S B boundary edgeCount loopCount edges loops V →
      (edgeCount : ℝ) =
        ((Set.ncard
            (projectiveCrossingSet D S B ∩ frontier D) : ℕ) : ℝ) / 2 +
          ∑ v ∈ V,
            ((analyticOrderNatAt (projectiveDelta S B) v + 1 : ℕ) : ℝ)

end MathlibPlus.Open.ResearchFormalization.ExactRegularEdgeCount15407
