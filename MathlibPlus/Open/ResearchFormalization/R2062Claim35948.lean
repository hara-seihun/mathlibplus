import MathlibPlus.Open.ResearchFormalization.R2062Claim35951

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35948

open MathlibPlus.Open.ResearchFormalization.R2062Claim35951

noncomputable section

abbrev Point := MathlibPlus.Open.ResearchFormalization.R2062Claim35951.Point

def claim35948 : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
      planarDiameterMinimizer n X D →
        unitTriangleFree X →
          activeConnected X D →
            ∀ a b : Point, activeBridge X D a b →
              ∀ (a' b' : Point) (W Z : Set Point),
                ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) →
                  bridgeCut X D a' b' W Z →
                    2 ≤ W.ncard →
                      ∀ (thetaPos thetaNeg : ℝ),
                        firstPositiveEvent X W Z D a' b' thetaPos →
                          firstNegativeEvent X W Z D a' b' thetaNeg →
                            planarDiameterMinimizer n
                                (movedConfiguration X W Z a' thetaPos) D ∧
                              planarDiameterMinimizer n
                                (movedConfiguration X W Z a' thetaNeg) D

end

end MathlibPlus.Open.ResearchFormalization.R2062Claim35948
