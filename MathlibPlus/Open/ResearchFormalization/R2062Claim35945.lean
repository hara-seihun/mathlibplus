import MathlibPlus.Open.ResearchFormalization.R2062Claim35951

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35945

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2062Claim35951

/-- Claim 35945: every active bridge in the stated planar minimizer setup has
an oriented connected bridge cut whose chosen `W` side has at least two
vertices. -/
def claim35945_planarBridgeSetup : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
    planarDiameterMinimizer n X D →
    unitTriangleFree X →
    activeConnected X D →
    ∀ a b : Point, activeBridge X D a b →
      ∃ a' b' : Point, ∃ W Z : Set Point,
        ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
          bridgeCut X D a' b' W Z ∧
            2 ≤ W.ncard

end

end MathlibPlus.Open.ResearchFormalization.R2062Claim35945
