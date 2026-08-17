import MathlibPlus.Open.ResearchFormalization.R2062Claim35951

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35949

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2062Claim35951

/-- Claim 35949: for either kind of first rotational event, the new cross
active edge and the two internal active paths close a cycle through the old
bridge; a triangle-free endpoint therefore no longer has that active bridge. -/
def claim35949_safeCrossEdgeRemovesBridge : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
    planarDiameterMinimizer n X D →
    unitTriangleFree X →
    activeConnected X D →
    ∀ a b : Point, activeBridge X D a b →
      ∀ W Z : Set Point,
        bridgeCut X D a b W Z →
          ∀ theta : ℝ,
            (firstPositiveEvent X W Z D a b theta ∨
              firstNegativeEvent X W Z D a b theta) →
              newCrossCycle X W Z D a b theta ∧
                (unitTriangleFree (movedConfiguration X W Z a theta) →
                  ¬ activeBridge
                    (movedConfiguration X W Z a theta) D a b)

end

end MathlibPlus.Open.ResearchFormalization.R2062Claim35949
