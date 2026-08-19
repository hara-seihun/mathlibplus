import MathlibPlus.Open.ResearchFormalization.R2062Claim35951

namespace MathlibPlus.Open.ResearchFormalization.R2062Claim35950

open MathlibPlus.Open.ResearchFormalization.R2062Claim35951

noncomputable section

abbrev Point := MathlibPlus.Open.ResearchFormalization.R2062Claim35951.Point

noncomputable def unitTriangleAcrossCut35950
    (W Z : Set Point) (a : Point) (theta : ℝ) : Prop :=
  ∃ u v w : Point,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ((u ∈ W ∧ v ∈ W ∧ w ∈ Z ∧
          distance (rotateAbout a u theta) (rotateAbout a v theta) = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance (rotateAbout a v theta) w = 1) ∨
        (u ∈ W ∧ v ∈ Z ∧ w ∈ Z ∧
          distance (rotateAbout a u theta) v = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance v w = 1))

noncomputable def newCrossUnitEdge35950
    (W Z : Set Point) (a b : Point) (theta : ℝ)
    (u : Point) (z : Point) : Prop :=
  u ∈ W ∧ z ∈ Z ∧
    (u ≠ a ∨ z ≠ b) ∧
    distance (rotateAbout a u theta) z = 1

noncomputable def bridgeUnitTriangleBlocker35950
    (W Z : Set Point) (a b : Point) (theta : ℝ) : Prop :=
  ∃ u v w : Point,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ((u ∈ W ∧ v ∈ W ∧ w ∈ Z ∧
          ((u = a ∧ w = b) ∨ (v = a ∧ w = b)) ∧
          distance (rotateAbout a u theta) (rotateAbout a v theta) = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance (rotateAbout a v theta) w = 1 ∧
          (newCrossUnitEdge35950 W Z a b theta v w ∨
            newCrossUnitEdge35950 W Z a b theta u w)) ∨
        (u ∈ W ∧ v ∈ Z ∧ w ∈ Z ∧
          ((u = a ∧ v = b) ∨ (u = a ∧ w = b)) ∧
          distance (rotateAbout a u theta) v = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance v w = 1 ∧
          (newCrossUnitEdge35950 W Z a b theta u w ∨
            newCrossUnitEdge35950 W Z a b theta u v)))

noncomputable def bothNewCrossUnitEdges35950
    (W Z : Set Point) (a b : Point) (theta : ℝ) : Prop :=
  ∃ u v w : Point,
    u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      ((u ∈ W ∧ v ∈ W ∧ w ∈ Z ∧
          (u ≠ a ∨ w ≠ b) ∧ (v ≠ a ∨ w ≠ b) ∧
          distance (rotateAbout a u theta) (rotateAbout a v theta) = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance (rotateAbout a v theta) w = 1) ∨
        (u ∈ W ∧ v ∈ Z ∧ w ∈ Z ∧
          (u ≠ a ∨ v ≠ b) ∧ (u ≠ a ∨ w ≠ b) ∧
          distance (rotateAbout a u theta) v = 1 ∧
          distance (rotateAbout a u theta) w = 1 ∧
          distance v w = 1))

noncomputable def everyUnitTriangleSpansMovedCut35950
    (X W Z : Set Point) (a : Point) (theta : ℝ) : Prop :=
  ∀ u v w : Point,
    u ∈ movedConfiguration X W Z a theta →
    v ∈ movedConfiguration X W Z a theta →
    w ∈ movedConfiguration X W Z a theta →
    u ≠ v → u ≠ w → v ≠ w →
    distance u v = 1 → distance u w = 1 → distance v w = 1 →
    ((u ∈ movedSide W a theta ∧ v ∈ movedSide W a theta ∧ w ∈ Z) ∨
      (u ∈ movedSide W a theta ∧ w ∈ movedSide W a theta ∧ v ∈ Z) ∨
      (v ∈ movedSide W a theta ∧ u ∈ movedSide W a theta ∧ w ∈ Z) ∨
      (v ∈ movedSide W a theta ∧ w ∈ movedSide W a theta ∧ u ∈ Z) ∨
      (w ∈ movedSide W a theta ∧ u ∈ movedSide W a theta ∧ v ∈ Z) ∨
      (w ∈ movedSide W a theta ∧ v ∈ movedSide W a theta ∧ u ∈ Z))

/-- The conditional bridge-blocker dichotomy, retaining the two-cross-edge
cut geometry and the distinction between a unit bridge and a diameter bridge. -/
def triangleBlockerDichotomy_claim35950 : Prop :=
  ∀ (n : ℕ) (X : Set Point) (D : ℝ),
    3 ≤ n →
    planarDiameterMinimizer n X D →
    unitTriangleFree X →
    activeConnected X D →
    ∀ a b : Point, ∀ W Z : Set Point,
      bridgeCut X D a b W Z →
      2 ≤ W.ncard →
      ∀ thetaPos thetaNeg : ℝ,
        firstPositiveEvent X W Z D a b thetaPos →
        firstNegativeEvent X W Z D a b thetaNeg →
        endpointData n X W Z D a b thetaPos →
        endpointData n X W Z D a b thetaNeg →
        (safeEndpoint n X W Z D a b thetaPos ∨
          safeEndpoint n X W Z D a b thetaNeg ∨
          (unitTriangleAcrossCut35950 W Z a thetaPos ∧
            unitTriangleAcrossCut35950 W Z a thetaNeg)) ∧
        (∀ theta : ℝ,
          endpointData n X W Z D a b theta →
            ((∀ u v : Point, u ∈ W → v ∈ W →
                distance (rotateAbout a u theta) (rotateAbout a v theta) =
                  distance u v) ∧
              (unitTriangleFree (movedConfiguration X W Z a theta) ∨
              (everyUnitTriangleSpansMovedCut35950 X W Z a theta ∧
                unitTriangleAcrossCut35950 W Z a theta ∧
                ((distance a b = 1 ∧
                    bridgeUnitTriangleBlocker35950 W Z a b theta) ∨
                  (distance a b = D ∧
                    bothNewCrossUnitEdges35950 W Z a b theta))))))

end

end MathlibPlus.Open.ResearchFormalization.R2062Claim35950
