import Mathlib
import MathlibPlus.Open.ResearchFormalization.R2062Claim35951

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35947

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2062Claim35951

/-- Claim 35947: after choosing the nontrivial side of an active bridge, an
active neighbour on that side gives the full radial cross-distance interval;
the interval leaves the strict feasible annulus, and the finite event set has
first events in both rotational directions. -/
def claim35947_firstNewEventEachDirection : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
      planarDiameterMinimizer n X D →
        unitTriangleFree X →
          activeConnected X D →
            ∀ a b : Point, activeBridge X D a b →
              ∃ a' b' : Point, ∃ W Z : Set Point,
                ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
                  bridgeCut X D a' b' W Z ∧
                  2 ≤ W.ncard ∧
                  ∃ c : Point,
                    c ∈ W ∧ activeAdjacency X D a' c ∧ c ≠ a' ∧
                      let r := distance a' b'
                      let s := distance a' c
                      (r = 1 ∨ r = D) ∧
                        (s = 1 ∨ s = D) ∧
                        1 < distance c b' ∧ distance c b' < D ∧
                        Set.range (fun theta : ℝ =>
                          distance (rotateAbout a' c theta) b') =
                          Set.Icc |r - s| (r + s) ∧
                        ¬ (Set.Icc |r - s| (r + s) ⊆ Set.Ioo 1 D) ∧
                        Set.Nonempty {theta : ℝ |
                          0 ≤ theta ∧ theta ≤ 2 * Real.pi ∧
                            crossActivationEventAt X W Z D a' b' theta} ∧
                        Set.Finite {theta : ℝ |
                          0 ≤ theta ∧ theta ≤ 2 * Real.pi ∧
                            crossActivationEventAt X W Z D a' b' theta} ∧
                        (∃ thetaPos : ℝ,
                          firstPositiveEvent X W Z D a' b' thetaPos) ∧
                        (∃ thetaNeg : ℝ,
                          firstNegativeEvent X W Z D a' b' thetaNeg)

end
end MathlibPlus.Open.ResearchFormalization.R2062Claim35947
